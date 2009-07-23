/*
 *	Linux NET3:	GRE over IP protocol decoder.
 *
 *	Authors: Alexey Kuznetsov (kuznet@ms2.inr.ac.ru)
 *
 *	This program is free software; you can redistribute it and/or
 *	modify it under the terms of the GNU General Public License
 *	as published by the Free Software Foundation; either version
 *	2 of the License, or (at your option) any later version.
 *
 */

#include <linux/capability.h>
#include <linux/module.h>
#include <linux/types.h>
#include <linux/kernel.h>
#include <asm/uaccess.h>
#include <linux/skbuff.h>
#include <linux/netdevice.h>
#include <linux/in.h>
#include <linux/tcp.h>
#include <linux/udp.h>
#include <linux/if_arp.h>
#include <linux/mroute.h>
#include <linux/init.h>
#include <linux/in6.h>
#include <linux/inetdevice.h>
#include <linux/igmp.h>
#include <linux/netfilter_ipv4.h>
#include <linux/etherdevice.h>
#include <linux/if_ether.h>
#include <linux/version.h>
#include <linux/rbtree.h>
#include <linux/timer.h>
#include <linux/mutex.h>

#include <net/sock.h>
#include <net/ip.h>
#include <net/icmp.h>
#include <net/protocol.h>
#include <net/ipip.h>
#include <net/arp.h>
#include <net/checksum.h>
#include <net/dsfield.h>
#include <net/inet_ecn.h>
#include <net/xfrm.h>
#include <net/net_namespace.h>
#include <net/netns/generic.h>
#include <net/rtnetlink.h>

#ifdef CONFIG_IPV6
#include <net/ipv6.h>
#include <net/ip6_fib.h>
#include <net/ip6_route.h>
#endif

/*
 * Backport changes in include/ from the following commits:
 *
 * c19e654ddbe3831252f61e76a74d661e1a755530
 * gre: Add netlink interface
 *
 * e1a8000228e16212c93b23cfbed4d622e2ec7a6b
 * gre: Add Transparent Ethernet Bridging
 */
#if LINUX_VERSION_CODE < KERNEL_VERSION(2,6,28)
enum
{
	IFLA_GRE_UNSPEC,
	IFLA_GRE_LINK,
	IFLA_GRE_IFLAGS,
	IFLA_GRE_OFLAGS,
	IFLA_GRE_IKEY,
	IFLA_GRE_OKEY,
	IFLA_GRE_LOCAL,
	IFLA_GRE_REMOTE,
	IFLA_GRE_TTL,
	IFLA_GRE_TOS,
	IFLA_GRE_PMTUDISC,
	__IFLA_GRE_MAX,
};

#define IFLA_GRE_MAX   (__IFLA_GRE_MAX - 1)

#define ETH_P_TEB	0x6558		/* Trans Ether Bridging		*/
#endif

/*
   Problems & solutions
   --------------------

   1. The most important issue is detecting local dead loops.
   They would cause complete host lockup in transmit, which
   would be "resolved" by stack overflow or, if queueing is enabled,
   with infinite looping in net_bh.

   We cannot track such dead loops during route installation,
   it is infeasible task. The most general solutions would be
   to keep skb->encapsulation counter (sort of local ttl),
   and silently drop packet when it expires. It is the best
   solution, but it supposes maintaing new variable in ALL
   skb, even if no tunneling is used.

   Current solution: t->recursion lock breaks dead loops. It looks
   like dev->tbusy flag, but I preferred new variable, because
   the semantics is different. One day, when hard_start_xmit
   will be multithreaded we will have to use skb->encapsulation.



   2. Networking dead loops would not kill routers, but would really
   kill network. IP hop limit plays role of "t->recursion" in this case,
   if we copy it from packet being encapsulated to upper header.
   It is very good solution, but it introduces two problems:

   - Routing protocols, using packets with ttl=1 (OSPF, RIP2),
     do not work over tunnels.
   - traceroute does not work. I planned to relay ICMP from tunnel,
     so that this problem would be solved and traceroute output
     would even more informative. This idea appeared to be wrong:
     only Linux complies to rfc1812 now (yes, guys, Linux is the only
     true router now :-)), all routers (at least, in neighbourhood of mine)
     return only 8 bytes of payload. It is the end.

   Hence, if we want that OSPF worked or traceroute said something reasonable,
   we should search for another solution.

   One of them is to parse packet trying to detect inner encapsulation
   made by our node. It is difficult or even impossible, especially,
   taking into account fragmentation. TO be short, tt is not solution at all.

   Current solution: The solution was UNEXPECTEDLY SIMPLE.
   We force DF flag on tunnels with preconfigured hop limit,
   that is ALL. :-) Well, it does not remove the problem completely,
   but exponential growth of network traffic is changed to linear
   (branches, that exceed pmtu are pruned) and tunnel mtu
   fastly degrades to value <68, where looping stops.
   Yes, it is not good if there exists a router in the loop,
   which does not force DF, even when encapsulating packets have DF set.
   But it is not our problem! Nobody could accuse us, we made
   all that we could make. Even if it is your gated who injected
   fatal route to network, even if it were you who configured
   fatal static route: you are innocent. :-)



   3. Really, ipv4/ipip.c, ipv4/ip_gre.c and ipv6/sit.c contain
   practically identical code. It would be good to glue them
   together, but it is not very evident, how to make them modular.
   sit is integral part of IPv6, ipip and gre are naturally modular.
   We could extract common parts (hash table, ioctl etc)
   to a separate module (ip_tunnel.c).

   Alexey Kuznetsov.
 */

#define IPGRE_ISER(tunnel)	((tunnel)->dev->type == ARPHRD_ETHER && \
				ipv4_is_multicast((tunnel)->parms.iph.daddr))

struct er_vlan;

struct er_tunnel {
	struct rb_root		er_vlans;
	struct timer_list	er_timer;
	struct er_vlan *	er_defvlan;
};

static int ipgre_er_init(struct ip_tunnel *);
static int ipgre_er_postinit(struct ip_tunnel *);
static void ipgre_er_uninit(struct ip_tunnel *);

static void ipgre_er_routing(struct ip_tunnel *, struct sk_buff *);
static void ipgre_er_xmit(struct ip_tunnel *, struct sk_buff *, __be32);
static __be32 ipgre_er_dst(struct ip_tunnel *, struct sk_buff *);

static struct rtnl_link_ops ipgre_link_ops __read_mostly;
static int ipgre_tunnel_init(struct net_device *dev);
static void ipgre_tunnel_setup(struct net_device *dev);
static int ipgre_tunnel_bind_dev(struct net_device *dev);

/* Fallback tunnel: no source, no destination, no key, no options */

static int ipgre_fb_tunnel_init(struct net_device *dev);

#define HASH_SIZE  16

static int ipgre_net_id;
struct ipgre_net {
	struct ip_tunnel *tunnels[4][HASH_SIZE];

	struct net_device *fb_tunnel_dev;
};

/* Tunnel hash table */

/*
   4 hash tables:

   3: (remote,local)
   2: (remote,*)
   1: (*,local)
   0: (*,*)

   We require exact key match i.e. if a key is present in packet
   it will match only tunnel with the same key; if it is not present,
   it will match only keyless tunnel.

   All keysless packets, if not matched configured keyless tunnels
   will match fallback tunnel.
 */

#define HASH(addr) (((__force u32)addr^((__force u32)addr>>4))&0xF)

#define tunnels_r_l	tunnels[3]
#define tunnels_r	tunnels[2]
#define tunnels_l	tunnels[1]
#define tunnels_wc	tunnels[0]

static DEFINE_RWLOCK(ipgre_lock);
static DEFINE_MUTEX(ipgre_mtx);

/* Given src, dst and key, find appropriate for input tunnel. */

static struct ip_tunnel * ipgre_tunnel_lookup(struct net_device *dev,
					      __be32 remote, __be32 local,
					      __be32 key, __be16 gre_proto)
{
	struct net *net = dev_net(dev);
	int link = dev->ifindex;
	unsigned h0 = HASH(remote);
	unsigned h1 = HASH(key);
	struct ip_tunnel *t, *cand = NULL;
	struct ipgre_net *ign = net_generic(net, ipgre_net_id);
	int dev_type = (gre_proto == htons(ETH_P_TEB)) ?
		       ARPHRD_ETHER : ARPHRD_IPGRE;
	int score, cand_score = 4;

	for (t = ign->tunnels_r_l[h0^h1]; t; t = t->next) {
		if (local != t->parms.iph.saddr ||
		    remote != t->parms.iph.daddr ||
		    key != t->parms.i_key ||
		    !(t->dev->flags & IFF_UP))
			continue;

		if (t->dev->type != ARPHRD_IPGRE &&
		    t->dev->type != dev_type)
			continue;

		score = 0;
		if (t->parms.link != link)
			score |= 1;
		if (t->dev->type != dev_type)
			score |= 2;
		if (score == 0)
			return t;

		if (score < cand_score) {
			cand = t;
			cand_score = score;
		}
	}

	for (t = ign->tunnels_r[h0^h1]; t; t = t->next) {
		if (remote != t->parms.iph.daddr ||
		    key != t->parms.i_key ||
		    !(t->dev->flags & IFF_UP))
			continue;

		if (t->dev->type != ARPHRD_IPGRE &&
		    t->dev->type != dev_type)
			continue;

		score = 0;
		if (t->parms.link != link)
			score |= 1;
		if (t->dev->type != dev_type)
			score |= 2;
		if (score == 0)
			return t;

		if (score < cand_score) {
			cand = t;
			cand_score = score;
		}
	}

	for (t = ign->tunnels_l[h1]; t; t = t->next) {
		if (IPGRE_ISER(t) && key == t->parms.i_key &&
		    (t->dev->flags & IFF_UP) && t->dev->type == dev_type &&
		    t->parms.link == link)
			/* Ethernet Relay tunnel */
			return t;

		if ((local != t->parms.iph.saddr &&
		     (local != t->parms.iph.daddr ||
		      !ipv4_is_multicast(local))) ||
		    key != t->parms.i_key ||
		    !(t->dev->flags & IFF_UP))
			continue;

		if (t->dev->type != ARPHRD_IPGRE &&
		    t->dev->type != dev_type)
			continue;

		score = 0;
		if (t->parms.link != link)
			score |= 1;
		if (t->dev->type != dev_type)
			score |= 2;
		if (score == 0)
			return t;

		if (score < cand_score) {
			cand = t;
			cand_score = score;
		}
	}

	for (t = ign->tunnels_wc[h1]; t; t = t->next) {
		if (t->parms.i_key != key ||
		    !(t->dev->flags & IFF_UP))
			continue;

		if (t->dev->type != ARPHRD_IPGRE &&
		    t->dev->type != dev_type)
			continue;

		score = 0;
		if (t->parms.link != link)
			score |= 1;
		if (t->dev->type != dev_type)
			score |= 2;
		if (score == 0)
			return t;

		if (score < cand_score) {
			cand = t;
			cand_score = score;
		}
	}

	if (cand != NULL)
		return cand;

	if (ign->fb_tunnel_dev->flags & IFF_UP)
		return netdev_priv(ign->fb_tunnel_dev);

	return NULL;
}

static struct ip_tunnel **__ipgre_bucket(struct ipgre_net *ign,
		struct ip_tunnel_parm *parms)
{
	__be32 remote = parms->iph.daddr;
	__be32 local = parms->iph.saddr;
	__be32 key = parms->i_key;
	unsigned h = HASH(key);
	int prio = 0;

	if (local)
		prio |= 1;
	if (remote && !ipv4_is_multicast(remote)) {
		prio |= 2;
		h ^= HASH(remote);
	}

	return &ign->tunnels[prio][h];
}

static inline struct ip_tunnel **ipgre_bucket(struct ipgre_net *ign,
		struct ip_tunnel *t)
{
	return __ipgre_bucket(ign, &t->parms);
}

static void ipgre_tunnel_link(struct ipgre_net *ign, struct ip_tunnel *t)
{
	struct ip_tunnel **tp = ipgre_bucket(ign, t);

	t->next = *tp;
	write_lock_bh(&ipgre_lock);
	*tp = t;
	write_unlock_bh(&ipgre_lock);
}

static void ipgre_tunnel_unlink(struct ipgre_net *ign, struct ip_tunnel *t)
{
	struct ip_tunnel **tp;

	for (tp = ipgre_bucket(ign, t); *tp; tp = &(*tp)->next) {
		if (t == *tp) {
			write_lock_bh(&ipgre_lock);
			*tp = t->next;
			write_unlock_bh(&ipgre_lock);
			break;
		}
	}
}

static struct ip_tunnel *ipgre_tunnel_find(struct net *net,
					   struct ip_tunnel_parm *parms,
					   int type)
{
	__be32 remote = parms->iph.daddr;
	__be32 local = parms->iph.saddr;
	__be32 key = parms->i_key;
	int link = parms->link;
	struct ip_tunnel *t, **tp;
	struct ipgre_net *ign = net_generic(net, ipgre_net_id);

	for (tp = __ipgre_bucket(ign, parms); (t = *tp) != NULL; tp = &t->next)
		if (local == t->parms.iph.saddr &&
		    remote == t->parms.iph.daddr &&
		    key == t->parms.i_key &&
		    link == t->parms.link &&
		    type == t->dev->type)
			break;

	return t;
}

static struct ip_tunnel * ipgre_tunnel_locate(struct net *net,
		struct ip_tunnel_parm *parms, int create)
{
	struct ip_tunnel *t, *nt;
	struct net_device *dev;
	char name[IFNAMSIZ];
	struct ipgre_net *ign = net_generic(net, ipgre_net_id);

	t = ipgre_tunnel_find(net, parms, ARPHRD_IPGRE);
	if (t || !create)
		return t;

	if (parms->name[0])
		strlcpy(name, parms->name, IFNAMSIZ);
	else
		sprintf(name, "gre%%d");

	dev = alloc_netdev(sizeof(*t) + sizeof(struct er_tunnel), name,
			   ipgre_tunnel_setup);
	if (!dev)
	  return NULL;

	dev_net_set(dev, net);

	if (strchr(name, '%')) {
		if (dev_alloc_name(dev, name) < 0)
			goto failed_free;
	}

	nt = netdev_priv(dev);
	nt->parms = *parms;
	dev->rtnl_link_ops = &ipgre_link_ops;

	dev->mtu = ipgre_tunnel_bind_dev(dev);

	if (register_netdevice(dev) < 0)
		goto failed_free;

	dev_hold(dev);
	ipgre_tunnel_link(ign, nt);
	return nt;

failed_free:
	free_netdev(dev);
	return NULL;
}

static void ipgre_tunnel_uninit(struct net_device *dev)
{
	struct net *net = dev_net(dev);
	struct ipgre_net *ign = net_generic(net, ipgre_net_id);
	struct ip_tunnel *tunnel = netdev_priv(dev);

	if (IPGRE_ISER(tunnel))
		ipgre_er_uninit(tunnel);

	ipgre_tunnel_unlink(ign, netdev_priv(dev));
	dev_put(dev);
}


static void ipgre_err(struct sk_buff *skb, u32 info)
{

/* All the routers (except for Linux) return only
   8 bytes of packet payload. It means, that precise relaying of
   ICMP in the real Internet is absolutely infeasible.

   Moreover, Cisco "wise men" put GRE key to the third word
   in GRE header. It makes impossible maintaining even soft state for keyed
   GRE tunnels with enabled checksum. Tell them "thank you".

   Well, I wonder, rfc1812 was written by Cisco employee,
   what the hell these idiots break standrads established
   by themself???
 */

	struct iphdr *iph = (struct iphdr*)skb->data;
	__be16	     *p = (__be16*)(skb->data+(iph->ihl<<2));
	int grehlen = (iph->ihl<<2) + 4;
	const int type = icmp_hdr(skb)->type;
	const int code = icmp_hdr(skb)->code;
	struct ip_tunnel *t;
	__be16 flags;

	flags = p[0];
	if (flags&(GRE_CSUM|GRE_KEY|GRE_SEQ|GRE_ROUTING|GRE_VERSION)) {
		if (flags&(GRE_VERSION|GRE_ROUTING))
			return;
		if (flags&GRE_KEY) {
			grehlen += 4;
			if (flags&GRE_CSUM)
				grehlen += 4;
		}
	}

	/* If only 8 bytes returned, keyed message will be dropped here */
	if (skb_headlen(skb) < grehlen)
		return;

	switch (type) {
	default:
	case ICMP_PARAMETERPROB:
		return;

	case ICMP_DEST_UNREACH:
		switch (code) {
		case ICMP_SR_FAILED:
		case ICMP_PORT_UNREACH:
			/* Impossible event. */
			return;
		case ICMP_FRAG_NEEDED:
			/* Soft state for pmtu is maintained by IP core. */
			return;
		default:
			/* All others are translated to HOST_UNREACH.
			   rfc2003 contains "deep thoughts" about NET_UNREACH,
			   I believe they are just ether pollution. --ANK
			 */
			break;
		}
		break;
	case ICMP_TIME_EXCEEDED:
		if (code != ICMP_EXC_TTL)
			return;
		break;
	}

	read_lock(&ipgre_lock);
	t = ipgre_tunnel_lookup(skb->dev, iph->daddr, iph->saddr,
				flags & GRE_KEY ?
				*(((__be32 *)p) + (grehlen / 4) - 1) : 0,
				p[1]);
	if (t == NULL || t->parms.iph.daddr == 0 ||
	    ipv4_is_multicast(t->parms.iph.daddr))
		goto out;

	if (t->parms.iph.ttl == 0 && type == ICMP_TIME_EXCEEDED)
		goto out;

	if (time_before(jiffies, t->err_time + IPTUNNEL_ERR_TIMEO))
		t->err_count++;
	else
		t->err_count = 1;
	t->err_time = jiffies;
out:
	read_unlock(&ipgre_lock);
	return;
}

static inline void ipgre_ecn_decapsulate(struct iphdr *iph, struct sk_buff *skb)
{
	if (INET_ECN_is_ce(iph->tos)) {
		if (skb->protocol == htons(ETH_P_IP)) {
			IP_ECN_set_ce(ip_hdr(skb));
		} else if (skb->protocol == htons(ETH_P_IPV6)) {
			IP6_ECN_set_ce(ipv6_hdr(skb));
		}
	}
}

static inline u8
ipgre_ecn_encapsulate(u8 tos, struct iphdr *old_iph, struct sk_buff *skb)
{
	u8 inner = 0;
	if (skb->protocol == htons(ETH_P_IP))
		inner = old_iph->tos;
	else if (skb->protocol == htons(ETH_P_IPV6))
		inner = ipv6_get_dsfield((struct ipv6hdr *)old_iph);
	return INET_ECN_encapsulate(tos, inner);
}

static int ipgre_rcv(struct sk_buff *skb)
{
	struct iphdr *iph;
	u8     *h;
	__be16    flags;
	__sum16   csum = 0;
	__be32 key = 0;
	u32    seqno = 0;
	struct ip_tunnel *tunnel;
	int    offset = 4;
	__be16 gre_proto;
	unsigned int len;
	__be32 daddr;

	if (!pskb_may_pull(skb, 16))
		goto drop_nolock;

	iph = ip_hdr(skb);
	h = skb->data;
	flags = *(__be16*)h;
	daddr = iph->daddr;

	if (flags&(GRE_CSUM|GRE_KEY|GRE_ROUTING|GRE_SEQ|GRE_VERSION)) {
		/* Version must be 0 */
		if (flags&GRE_VERSION)
			goto drop_nolock;

		if (flags&GRE_CSUM) {
			switch (skb->ip_summed) {
			case CHECKSUM_COMPLETE:
				csum = csum_fold(skb->csum);
				if (!csum)
					break;
				/* fall through */
			case CHECKSUM_NONE:
				skb->csum = 0;
				csum = __skb_checksum_complete(skb);
				skb->ip_summed = CHECKSUM_COMPLETE;
			}
			offset += 4;
		}
		if (flags&GRE_KEY) {
			key = *(__be32*)(h + offset);
			offset += 4;
		}
		if (flags&GRE_SEQ) {
			seqno = ntohl(*(__be32*)(h + offset));
			offset += 4;
		}
	}

	gre_proto = *(__be16 *)(h + 2);

	read_lock(&ipgre_lock);
	if ((tunnel = ipgre_tunnel_lookup(skb->dev,
					  iph->saddr, iph->daddr, key,
					  gre_proto))) {
		struct net_device_stats *stats = &tunnel->dev->stats;

		if (flags & GRE_ROUTING) {
			/*
			 * We do not support routing headers except for
			 * Ethernet Relay.
			 */
			if (!IPGRE_ISER(tunnel))
				goto drop;

			read_unlock(&ipgre_lock);
			skb_pull(skb, offset);
			ipgre_er_routing(tunnel, skb);
			kfree_skb(skb);
			return 0;
		}

		secpath_reset(skb);

		skb->protocol = gre_proto;
		/* WCCP version 1 and 2 protocol decoding.
		 * - Change protocol to IP
		 * - When dealing with WCCPv2, Skip extra 4 bytes in GRE header
		 */
		if (flags == 0 && gre_proto == htons(ETH_P_WCCP)) {
			skb->protocol = htons(ETH_P_IP);
			if ((*(h + offset) & 0xF0) != 0x40)
				offset += 4;
		}

		skb->mac_header = skb->network_header;
		__pskb_pull(skb, offset);
		skb_postpull_rcsum(skb, skb_transport_header(skb), offset);
		skb->pkt_type = PACKET_HOST;
#ifdef CONFIG_NET_IPGRE_BROADCAST
		if (ipv4_is_multicast(iph->daddr)) {
			/* Looped back packet, drop it! */
			if (skb->rtable->fl.iif == 0)
				goto drop;
			stats->multicast++;
			skb->pkt_type = PACKET_BROADCAST;
		}
#endif

		if (((flags&GRE_CSUM) && csum) ||
		    (!(flags&GRE_CSUM) && tunnel->parms.i_flags&GRE_CSUM)) {
			stats->rx_crc_errors++;
			stats->rx_errors++;
			goto drop;
		}
		if (tunnel->parms.i_flags&GRE_SEQ) {
			if (!(flags&GRE_SEQ) ||
			    (tunnel->i_seqno && (s32)(seqno - tunnel->i_seqno) < 0)) {
				stats->rx_fifo_errors++;
				stats->rx_errors++;
				goto drop;
			}
			tunnel->i_seqno = seqno + 1;
		}

		len = skb->len;

		/* Warning: All skb pointers will be invalidated! */
		if (tunnel->dev->type == ARPHRD_ETHER) {
			if (!pskb_may_pull(skb, ETH_HLEN)) {
				stats->rx_length_errors++;
				stats->rx_errors++;
				goto drop;
			}

			iph = ip_hdr(skb);
			skb->protocol = eth_type_trans(skb, tunnel->dev);
			skb_postpull_rcsum(skb, eth_hdr(skb), ETH_HLEN);
		}

		stats->rx_packets++;
		stats->rx_bytes += len;
		skb->dev = tunnel->dev;
		dst_release(skb->dst);
		skb->dst = NULL;
		nf_reset(skb);

		skb_reset_network_header(skb);
		ipgre_ecn_decapsulate(iph, skb);

		if (IPGRE_ISER(tunnel))
			ipgre_er_xmit(tunnel, skb, daddr);
		netif_rx(skb);
		read_unlock(&ipgre_lock);
		return(0);
	}
	icmp_send(skb, ICMP_DEST_UNREACH, ICMP_PORT_UNREACH, 0);

drop:
	read_unlock(&ipgre_lock);
drop_nolock:
	kfree_skb(skb);
	return(0);
}

static int ipgre_tunnel_xmit(struct sk_buff *skb, struct net_device *dev)
{
	struct ip_tunnel *tunnel = netdev_priv(dev);
	struct net_device_stats *stats = &tunnel->dev->stats;
	struct iphdr  *old_iph = ip_hdr(skb);
	struct iphdr  *tiph;
	u8     tos;
	__be16 df;
	struct rtable *rt;     			/* Route to the other host */
	struct net_device *tdev;			/* Device to other host */
	struct iphdr  *iph;			/* Our new IP header */
	unsigned int max_headroom;		/* The extra header space needed */
	int    gre_hlen;
	__be32 dst;
	int    mtu;

	if (tunnel->recursion++) {
		stats->collisions++;
		goto tx_error;
	}

	if (dev->type == ARPHRD_ETHER)
		IPCB(skb)->flags = 0;

	if (dev->header_ops && dev->type == ARPHRD_IPGRE) {
		gre_hlen = 0;
		tiph = (struct iphdr*)skb->data;
	} else {
		gre_hlen = tunnel->hlen;
		tiph = &tunnel->parms.iph;
	}

	if ((dst = tiph->daddr) == 0) {
		/* NBMA tunnel */

		if (skb->dst == NULL) {
			stats->tx_fifo_errors++;
			goto tx_error;
		}

		if (skb->protocol == htons(ETH_P_IP)) {
			rt = skb->rtable;
			if ((dst = rt->rt_gateway) == 0)
				goto tx_error_icmp;
		}
#ifdef CONFIG_IPV6
		else if (skb->protocol == htons(ETH_P_IPV6)) {
			struct in6_addr *addr6;
			int addr_type;
			struct neighbour *neigh = skb->dst->neighbour;

			if (neigh == NULL)
				goto tx_error;

			addr6 = (struct in6_addr*)&neigh->primary_key;
			addr_type = ipv6_addr_type(addr6);

			if (addr_type == IPV6_ADDR_ANY) {
				addr6 = &ipv6_hdr(skb)->daddr;
				addr_type = ipv6_addr_type(addr6);
			}

			if ((addr_type & IPV6_ADDR_COMPATv4) == 0)
				goto tx_error_icmp;

			dst = addr6->s6_addr32[3];
		}
#endif
		else
			goto tx_error;
	}

	if (IPGRE_ISER(tunnel)) {
		skb_reset_mac_header(skb);
		if ((dst = ipgre_er_dst(tunnel, skb)) == 0)
			goto tx_error;
	}

	tos = tiph->tos;
	if (tos&1) {
		if (skb->protocol == htons(ETH_P_IP))
			tos = old_iph->tos;
		tos &= ~1;
	}

	{
		struct flowi fl = { .oif = tunnel->parms.link,
				    .nl_u = { .ip4_u =
					      { .daddr = dst,
						.saddr = tiph->saddr,
						.tos = RT_TOS(tos) } },
				    .proto = IPPROTO_GRE };
		if (ip_route_output_key(dev_net(dev), &rt, &fl)) {
			stats->tx_carrier_errors++;
			goto tx_error;
		}
	}
	tdev = rt->u.dst.dev;

	if (tdev == dev) {
		ip_rt_put(rt);
		stats->collisions++;
		goto tx_error;
	}

	df = tiph->frag_off;
	if (df)
		mtu = dst_mtu(&rt->u.dst) - dev->hard_header_len - tunnel->hlen;
	else
		mtu = skb->dst ? dst_mtu(skb->dst) : dev->mtu;

	if (skb->dst)
		skb->dst->ops->update_pmtu(skb->dst, mtu);

	if (skb->protocol == htons(ETH_P_IP)) {
		df |= (old_iph->frag_off&htons(IP_DF));

		if ((old_iph->frag_off&htons(IP_DF)) &&
		    mtu < ntohs(old_iph->tot_len)) {
			icmp_send(skb, ICMP_DEST_UNREACH, ICMP_FRAG_NEEDED, htonl(mtu));
			ip_rt_put(rt);
			goto tx_error;
		}
	}
#ifdef CONFIG_IPV6
	else if (skb->protocol == htons(ETH_P_IPV6)) {
		struct rt6_info *rt6 = (struct rt6_info*)skb->dst;

		if (rt6 && mtu < dst_mtu(skb->dst) && mtu >= IPV6_MIN_MTU) {
			if ((tunnel->parms.iph.daddr &&
			     !ipv4_is_multicast(tunnel->parms.iph.daddr)) ||
			    rt6->rt6i_dst.plen == 128) {
				rt6->rt6i_flags |= RTF_MODIFIED;
				skb->dst->metrics[RTAX_MTU-1] = mtu;
			}
		}

		if (mtu >= IPV6_MIN_MTU && mtu < skb->len - tunnel->hlen + gre_hlen) {
			icmpv6_send(skb, ICMPV6_PKT_TOOBIG, 0, mtu, dev);
			ip_rt_put(rt);
			goto tx_error;
		}
	}
#endif

	if (tunnel->err_count > 0) {
		if (time_before(jiffies,
				tunnel->err_time + IPTUNNEL_ERR_TIMEO)) {
			tunnel->err_count--;

			dst_link_failure(skb);
		} else
			tunnel->err_count = 0;
	}

	max_headroom = LL_RESERVED_SPACE(tdev) + gre_hlen;

	if (skb_headroom(skb) < max_headroom || skb_shared(skb)||
	    (skb_cloned(skb) && !skb_clone_writable(skb, 0))) {
		struct sk_buff *new_skb = skb_realloc_headroom(skb, max_headroom);
		if (!new_skb) {
			ip_rt_put(rt);
			stats->tx_dropped++;
			dev_kfree_skb(skb);
			tunnel->recursion--;
			return 0;
		}
		if (skb->sk)
			skb_set_owner_w(new_skb, skb->sk);
		dev_kfree_skb(skb);
		skb = new_skb;
		old_iph = ip_hdr(skb);
	}

	skb_reset_transport_header(skb);
	skb_push(skb, gre_hlen);
	skb_reset_network_header(skb);
	memset(&(IPCB(skb)->opt), 0, sizeof(IPCB(skb)->opt));
	IPCB(skb)->flags &= ~(IPSKB_XFRM_TUNNEL_SIZE | IPSKB_XFRM_TRANSFORMED |
			      IPSKB_REROUTED);
	dst_release(skb->dst);
	skb->dst = &rt->u.dst;

	/*
	 *	Push down and install the IPIP header.
	 */

	iph 			=	ip_hdr(skb);
	iph->version		=	4;
	iph->ihl		=	sizeof(struct iphdr) >> 2;
	iph->frag_off		=	df;
	iph->protocol		=	IPPROTO_GRE;
	iph->tos		=	ipgre_ecn_encapsulate(tos, old_iph, skb);
	iph->daddr		=	rt->rt_dst;
	iph->saddr		=	rt->rt_src;

	if ((iph->ttl = tiph->ttl) == 0) {
		if (skb->protocol == htons(ETH_P_IP))
			iph->ttl = old_iph->ttl;
#ifdef CONFIG_IPV6
		else if (skb->protocol == htons(ETH_P_IPV6))
			iph->ttl = ((struct ipv6hdr*)old_iph)->hop_limit;
#endif
		else
			iph->ttl = dst_metric(&rt->u.dst, RTAX_HOPLIMIT);
	}

	((__be16 *)(iph + 1))[0] = tunnel->parms.o_flags;
	((__be16 *)(iph + 1))[1] = (dev->type == ARPHRD_ETHER) ?
				   htons(ETH_P_TEB) : skb->protocol;

	if (tunnel->parms.o_flags&(GRE_KEY|GRE_CSUM|GRE_SEQ)) {
		__be32 *ptr = (__be32*)(((u8*)iph) + tunnel->hlen - 4);

		if (tunnel->parms.o_flags&GRE_SEQ) {
			++tunnel->o_seqno;
			*ptr = htonl(tunnel->o_seqno);
			ptr--;
		}
		if (tunnel->parms.o_flags&GRE_KEY) {
			*ptr = tunnel->parms.o_key;
			ptr--;
		}
		if (tunnel->parms.o_flags&GRE_CSUM) {
			*ptr = 0;
			*(__sum16*)ptr = ip_compute_csum((void*)(iph+1), skb->len - sizeof(struct iphdr));
		}
	}

	nf_reset(skb);

	IPTUNNEL_XMIT();
	tunnel->recursion--;
	return 0;

tx_error_icmp:
	dst_link_failure(skb);

tx_error:
	stats->tx_errors++;
	dev_kfree_skb(skb);
	tunnel->recursion--;
	return 0;
}

static int ipgre_tunnel_bind_dev(struct net_device *dev)
{
	struct net_device *tdev = NULL;
	struct ip_tunnel *tunnel;
	struct iphdr *iph;
	int hlen = LL_MAX_HEADER;
	int mtu = ETH_DATA_LEN;
	int addend = sizeof(struct iphdr) + 4;

	tunnel = netdev_priv(dev);
	iph = &tunnel->parms.iph;

	/* Guess output device to choose reasonable mtu and needed_headroom */

	if (iph->daddr) {
		struct flowi fl = { .oif = tunnel->parms.link,
				    .nl_u = { .ip4_u =
					      { .daddr = iph->daddr,
						.saddr = iph->saddr,
						.tos = RT_TOS(iph->tos) } },
				    .proto = IPPROTO_GRE };
		struct rtable *rt;
		if (!ip_route_output_key(dev_net(dev), &rt, &fl)) {
			tdev = rt->u.dst.dev;
			ip_rt_put(rt);
		}

		if (dev->type != ARPHRD_ETHER)
			dev->flags |= IFF_POINTOPOINT;
	}

	if (!tdev && tunnel->parms.link)
		tdev = __dev_get_by_index(dev_net(dev), tunnel->parms.link);

	if (tdev) {
		tunnel->parms.link = tdev->ifindex;
		hlen = tdev->hard_header_len + tdev->needed_headroom;
		mtu = tdev->mtu;
	}
	dev->iflink = tunnel->parms.link;

	/* Precalculate GRE options length */
	if (tunnel->parms.o_flags&(GRE_CSUM|GRE_KEY|GRE_SEQ)) {
		if (tunnel->parms.o_flags&GRE_CSUM)
			addend += 4;
		if (tunnel->parms.o_flags&GRE_KEY)
			addend += 4;
		if (tunnel->parms.o_flags&GRE_SEQ)
			addend += 4;
	}
	dev->needed_headroom = addend + hlen;
	mtu -= dev->hard_header_len - addend;

	if (mtu < 68)
		mtu = 68;

	tunnel->hlen = addend;

	return mtu;
}

static int
ipgre_tunnel_ioctl (struct net_device *dev, struct ifreq *ifr, int cmd)
{
	int err = 0;
	struct ip_tunnel_parm p;
	struct ip_tunnel *t;
	struct net *net = dev_net(dev);
	struct ipgre_net *ign = net_generic(net, ipgre_net_id);

	switch (cmd) {
	case SIOCGETTUNNEL:
		t = NULL;
		if (dev == ign->fb_tunnel_dev) {
			if (copy_from_user(&p, ifr->ifr_ifru.ifru_data, sizeof(p))) {
				err = -EFAULT;
				break;
			}
			t = ipgre_tunnel_locate(net, &p, 0);
		}
		if (t == NULL)
			t = netdev_priv(dev);
		memcpy(&p, &t->parms, sizeof(p));
		if (copy_to_user(ifr->ifr_ifru.ifru_data, &p, sizeof(p)))
			err = -EFAULT;
		break;

	case SIOCADDTUNNEL:
	case SIOCCHGTUNNEL:
		err = -EPERM;
		if (!capable(CAP_NET_ADMIN))
			goto done;

		err = -EFAULT;
		if (copy_from_user(&p, ifr->ifr_ifru.ifru_data, sizeof(p)))
			goto done;

		err = -EINVAL;
		if (p.iph.version != 4 || p.iph.protocol != IPPROTO_GRE ||
		    p.iph.ihl != 5 || (p.iph.frag_off&htons(~IP_DF)) ||
		    ((p.i_flags|p.o_flags)&(GRE_VERSION|GRE_ROUTING)))
			goto done;
		if (p.iph.ttl)
			p.iph.frag_off |= htons(IP_DF);

		if (!(p.i_flags&GRE_KEY))
			p.i_key = 0;
		if (!(p.o_flags&GRE_KEY))
			p.o_key = 0;

		t = ipgre_tunnel_locate(net, &p, cmd == SIOCADDTUNNEL);

		if (dev != ign->fb_tunnel_dev && cmd == SIOCCHGTUNNEL) {
			if (t != NULL) {
				if (t->dev != dev) {
					err = -EEXIST;
					break;
				}
			} else {
				unsigned nflags=0;

				t = netdev_priv(dev);

				if (ipv4_is_multicast(p.iph.daddr))
					nflags = IFF_BROADCAST;
				else if (p.iph.daddr)
					nflags = IFF_POINTOPOINT;

				if ((dev->flags^nflags)&(IFF_POINTOPOINT|IFF_BROADCAST)) {
					err = -EINVAL;
					break;
				}
				ipgre_tunnel_unlink(ign, t);
				t->parms.iph.saddr = p.iph.saddr;
				t->parms.iph.daddr = p.iph.daddr;
				t->parms.i_key = p.i_key;
				t->parms.o_key = p.o_key;
				memcpy(dev->dev_addr, &p.iph.saddr, 4);
				memcpy(dev->broadcast, &p.iph.daddr, 4);
				ipgre_tunnel_link(ign, t);
				netdev_state_change(dev);
			}
		}

		if (t) {
			err = 0;
			if (cmd == SIOCCHGTUNNEL) {
				t->parms.iph.ttl = p.iph.ttl;
				t->parms.iph.tos = p.iph.tos;
				t->parms.iph.frag_off = p.iph.frag_off;
				if (t->parms.link != p.link) {
					t->parms.link = p.link;
					dev->mtu = ipgre_tunnel_bind_dev(dev);
					netdev_state_change(dev);
				}
			}
			if (copy_to_user(ifr->ifr_ifru.ifru_data, &t->parms, sizeof(p)))
				err = -EFAULT;
		} else
			err = (cmd == SIOCADDTUNNEL ? -ENOBUFS : -ENOENT);
		break;

	case SIOCDELTUNNEL:
		err = -EPERM;
		if (!capable(CAP_NET_ADMIN))
			goto done;

		if (dev == ign->fb_tunnel_dev) {
			err = -EFAULT;
			if (copy_from_user(&p, ifr->ifr_ifru.ifru_data, sizeof(p)))
				goto done;
			err = -ENOENT;
			if ((t = ipgre_tunnel_locate(net, &p, 0)) == NULL)
				goto done;
			err = -EPERM;
			if (t == netdev_priv(ign->fb_tunnel_dev))
				goto done;
			dev = t->dev;
		}
		unregister_netdevice(dev);
		err = 0;
		break;

	default:
		err = -EINVAL;
	}

done:
	return err;
}

static int ipgre_tunnel_change_mtu(struct net_device *dev, int new_mtu)
{
	struct ip_tunnel *tunnel = netdev_priv(dev);
	if (new_mtu < 68 ||
	    new_mtu > 0xFFF8 - dev->hard_header_len - tunnel->hlen)
		return -EINVAL;
	dev->mtu = new_mtu;
	return 0;
}

/* Nice toy. Unfortunately, useless in real life :-)
   It allows to construct virtual multiprotocol broadcast "LAN"
   over the Internet, provided multicast routing is tuned.


   I have no idea was this bicycle invented before me,
   so that I had to set ARPHRD_IPGRE to a random value.
   I have an impression, that Cisco could make something similar,
   but this feature is apparently missing in IOS<=11.2(8).

   I set up 10.66.66/24 and fec0:6666:6666::0/96 as virtual networks
   with broadcast 224.66.66.66. If you have access to mbone, play with me :-)

   ping -t 255 224.66.66.66

   If nobody answers, mbone does not work.

   ip tunnel add Universe mode gre remote 224.66.66.66 local <Your_real_addr> ttl 255
   ip addr add 10.66.66.<somewhat>/24 dev Universe
   ifconfig Universe up
   ifconfig Universe add fe80::<Your_real_addr>/10
   ifconfig Universe add fec0:6666:6666::<Your_real_addr>/96
   ftp 10.66.66.66
   ...
   ftp fec0:6666:6666::193.233.7.65
   ...

 */

static int ipgre_header(struct sk_buff *skb, struct net_device *dev,
			unsigned short type,
			const void *daddr, const void *saddr, unsigned len)
{
	struct ip_tunnel *t = netdev_priv(dev);
	struct iphdr *iph = (struct iphdr *)skb_push(skb, t->hlen);
	__be16 *p = (__be16*)(iph+1);

	memcpy(iph, &t->parms.iph, sizeof(struct iphdr));
	p[0]		= t->parms.o_flags;
	p[1]		= htons(type);

	/*
	 *	Set the source hardware address.
	 */

	if (saddr)
		memcpy(&iph->saddr, saddr, 4);

	if (daddr) {
		memcpy(&iph->daddr, daddr, 4);
		return t->hlen;
	}
	if (iph->daddr && !ipv4_is_multicast(iph->daddr))
		return t->hlen;

	return -t->hlen;
}

static int ipgre_header_parse(const struct sk_buff *skb, unsigned char *haddr)
{
	struct iphdr *iph = (struct iphdr*) skb_mac_header(skb);
	memcpy(haddr, &iph->saddr, 4);
	return 4;
}

static const struct header_ops ipgre_header_ops = {
	.create	= ipgre_header,
	.parse	= ipgre_header_parse,
};

#ifdef CONFIG_NET_IPGRE_BROADCAST
static int ipgre_open(struct net_device *dev)
{
	struct ip_tunnel *t = netdev_priv(dev);

	if (ipv4_is_multicast(t->parms.iph.daddr)) {
		struct flowi fl = { .oif = t->parms.link,
				    .nl_u = { .ip4_u =
					      { .daddr = t->parms.iph.daddr,
						.saddr = t->parms.iph.saddr,
						.tos = RT_TOS(t->parms.iph.tos) } },
				    .proto = IPPROTO_GRE };
		struct rtable *rt;
		if (ip_route_output_key(dev_net(dev), &rt, &fl))
			return -EADDRNOTAVAIL;
		dev = rt->u.dst.dev;
		ip_rt_put(rt);
		if (__in_dev_get_rtnl(dev) == NULL)
			return -EADDRNOTAVAIL;
		t->mlink = dev->ifindex;
		ip_mc_inc_group(__in_dev_get_rtnl(dev), t->parms.iph.daddr);
	}
	return 0;
}

static int ipgre_close(struct net_device *dev)
{
	struct ip_tunnel *t = netdev_priv(dev);
	if (ipv4_is_multicast(t->parms.iph.daddr) && t->mlink) {
		struct in_device *in_dev;
		in_dev = inetdev_by_index(dev_net(dev), t->mlink);
		if (in_dev) {
			ip_mc_dec_group(in_dev, t->parms.iph.daddr);
			in_dev_put(in_dev);
		}
	}
	return 0;
}

#endif

static void ipgre_tunnel_setup(struct net_device *dev)
{
	dev->init		= ipgre_tunnel_init;
	dev->uninit		= ipgre_tunnel_uninit;
	dev->destructor 	= free_netdev;
	dev->hard_start_xmit	= ipgre_tunnel_xmit;
	dev->do_ioctl		= ipgre_tunnel_ioctl;
	dev->change_mtu		= ipgre_tunnel_change_mtu;

	dev->type		= ARPHRD_IPGRE;
	dev->needed_headroom 	= LL_MAX_HEADER + sizeof(struct iphdr) + 4;
	dev->mtu		= ETH_DATA_LEN - sizeof(struct iphdr) - 4;
	dev->flags		= IFF_NOARP;
	dev->iflink		= 0;
	dev->addr_len		= 4;
	dev->features		|= NETIF_F_NETNS_LOCAL;
}

static int ipgre_tunnel_init(struct net_device *dev)
{
	struct ip_tunnel *tunnel;
	struct iphdr *iph;

	tunnel = netdev_priv(dev);
	iph = &tunnel->parms.iph;

	tunnel->dev = dev;
	strcpy(tunnel->parms.name, dev->name);

	memcpy(dev->dev_addr, &tunnel->parms.iph.saddr, 4);
	memcpy(dev->broadcast, &tunnel->parms.iph.daddr, 4);

	if (iph->daddr) {
#ifdef CONFIG_NET_IPGRE_BROADCAST
		if (ipv4_is_multicast(iph->daddr)) {
			if (!iph->saddr)
				return -EINVAL;
			dev->flags = IFF_BROADCAST;
			dev->header_ops = &ipgre_header_ops;
			dev->open = ipgre_open;
			dev->stop = ipgre_close;
		}
#endif
	} else
		dev->header_ops = &ipgre_header_ops;

	return 0;
}

static int ipgre_fb_tunnel_init(struct net_device *dev)
{
	struct ip_tunnel *tunnel = netdev_priv(dev);
	struct iphdr *iph = &tunnel->parms.iph;
	struct ipgre_net *ign = net_generic(dev_net(dev), ipgre_net_id);

	tunnel->dev = dev;
	strcpy(tunnel->parms.name, dev->name);

	iph->version		= 4;
	iph->protocol		= IPPROTO_GRE;
	iph->ihl		= 5;
	tunnel->hlen		= sizeof(struct iphdr) + 4;

	dev_hold(dev);
	ign->tunnels_wc[0]	= tunnel;
	return 0;
}


static struct net_protocol ipgre_protocol = {
	.handler	=	ipgre_rcv,
	.err_handler	=	ipgre_err,
	.netns_ok	=	1,
};

static void ipgre_destroy_tunnels(struct ipgre_net *ign)
{
	int prio;

	for (prio = 0; prio < 4; prio++) {
		int h;
		for (h = 0; h < HASH_SIZE; h++) {
			struct ip_tunnel *t;
			while ((t = ign->tunnels[prio][h]) != NULL)
				unregister_netdevice(t->dev);
		}
	}
}

static int ipgre_init_net(struct net *net)
{
	int err;
	struct ipgre_net *ign;

	err = -ENOMEM;
	ign = kzalloc(sizeof(struct ipgre_net), GFP_KERNEL);
	if (ign == NULL)
		goto err_alloc;

	err = net_assign_generic(net, ipgre_net_id, ign);
	if (err < 0)
		goto err_assign;

	ign->fb_tunnel_dev = alloc_netdev(sizeof(struct ip_tunnel), "gre0",
					   ipgre_tunnel_setup);
	if (!ign->fb_tunnel_dev) {
		err = -ENOMEM;
		goto err_alloc_dev;
	}

	ign->fb_tunnel_dev->init = ipgre_fb_tunnel_init;
	dev_net_set(ign->fb_tunnel_dev, net);
	ign->fb_tunnel_dev->rtnl_link_ops = &ipgre_link_ops;

	if ((err = register_netdev(ign->fb_tunnel_dev)))
		goto err_reg_dev;

	return 0;

err_reg_dev:
	free_netdev(ign->fb_tunnel_dev);
err_alloc_dev:
	/* nothing */
err_assign:
	kfree(ign);
err_alloc:
	return err;
}

static void ipgre_exit_net(struct net *net)
{
	struct ipgre_net *ign;

	ign = net_generic(net, ipgre_net_id);
	rtnl_lock();
	ipgre_destroy_tunnels(ign);
	rtnl_unlock();
	kfree(ign);
}

static struct pernet_operations ipgre_net_ops = {
	.init = ipgre_init_net,
	.exit = ipgre_exit_net,
};

static int ipgre_tunnel_validate(struct nlattr *tb[], struct nlattr *data[])
{
	__be16 flags;

	if (!data)
		return 0;

	flags = 0;
	if (data[IFLA_GRE_IFLAGS])
		flags |= nla_get_be16(data[IFLA_GRE_IFLAGS]);
	if (data[IFLA_GRE_OFLAGS])
		flags |= nla_get_be16(data[IFLA_GRE_OFLAGS]);
	if (flags & (GRE_VERSION|GRE_ROUTING))
		return -EINVAL;

	return 0;
}

static int ipgre_tap_validate(struct nlattr *tb[], struct nlattr *data[])
{
	__be32 daddr;

	if (tb[IFLA_ADDRESS]) {
		if (nla_len(tb[IFLA_ADDRESS]) != ETH_ALEN)
			return -EINVAL;
		if (!is_valid_ether_addr(nla_data(tb[IFLA_ADDRESS])))
			return -EADDRNOTAVAIL;
	}

	if (!data)
		goto out;

	if (data[IFLA_GRE_REMOTE]) {
		memcpy(&daddr, nla_data(data[IFLA_GRE_REMOTE]), 4);
		if (!daddr)
			return -EINVAL;
	}

out:
	return ipgre_tunnel_validate(tb, data);
}

static void ipgre_netlink_parms(struct nlattr *data[],
				struct ip_tunnel_parm *parms)
{
	memset(parms, 0, sizeof(*parms));

	parms->iph.protocol = IPPROTO_GRE;

	if (!data)
		return;

	if (data[IFLA_GRE_LINK])
		parms->link = nla_get_u32(data[IFLA_GRE_LINK]);

	if (data[IFLA_GRE_IFLAGS])
		parms->i_flags = nla_get_be16(data[IFLA_GRE_IFLAGS]);

	if (data[IFLA_GRE_OFLAGS])
		parms->o_flags = nla_get_be16(data[IFLA_GRE_OFLAGS]);

	if (data[IFLA_GRE_IKEY])
		parms->i_key = nla_get_be32(data[IFLA_GRE_IKEY]);

	if (data[IFLA_GRE_OKEY])
		parms->o_key = nla_get_be32(data[IFLA_GRE_OKEY]);

	if (data[IFLA_GRE_LOCAL])
		parms->iph.saddr = nla_get_be32(data[IFLA_GRE_LOCAL]);

	if (data[IFLA_GRE_REMOTE])
		parms->iph.daddr = nla_get_be32(data[IFLA_GRE_REMOTE]);

	if (data[IFLA_GRE_TTL])
		parms->iph.ttl = nla_get_u8(data[IFLA_GRE_TTL]);

	if (data[IFLA_GRE_TOS])
		parms->iph.tos = nla_get_u8(data[IFLA_GRE_TOS]);

	if (!data[IFLA_GRE_PMTUDISC] || nla_get_u8(data[IFLA_GRE_PMTUDISC]))
		parms->iph.frag_off = htons(IP_DF);
}

static int ipgre_tap_init(struct net_device *dev)
{
	struct ip_tunnel *tunnel;

	tunnel = netdev_priv(dev);

	tunnel->dev = dev;
	strcpy(tunnel->parms.name, dev->name);

	ipgre_tunnel_bind_dev(dev);

	if (IPGRE_ISER(tunnel))
		ipgre_er_init(tunnel);

	return 0;
}

static void ipgre_tap_setup(struct net_device *dev)
{

	ether_setup(dev);

	dev->init		= ipgre_tap_init;
	dev->uninit		= ipgre_tunnel_uninit;
	dev->destructor 	= free_netdev;
	dev->hard_start_xmit	= ipgre_tunnel_xmit;
	dev->change_mtu		= ipgre_tunnel_change_mtu;

	dev->iflink		= 0;
	dev->features		|= NETIF_F_NETNS_LOCAL;
}

static int ipgre_newlink(struct net_device *dev, struct nlattr *tb[],
			 struct nlattr *data[])
{
	struct ip_tunnel *nt;
	struct net *net = dev_net(dev);
	struct ipgre_net *ign = net_generic(net, ipgre_net_id);
	int mtu;
	int err;

	nt = netdev_priv(dev);
	ipgre_netlink_parms(data, &nt->parms);

	if (ipgre_tunnel_find(net, &nt->parms, dev->type))
		return -EEXIST;

	if (dev->type == ARPHRD_ETHER && !tb[IFLA_ADDRESS])
		random_ether_addr(dev->dev_addr);

	mtu = ipgre_tunnel_bind_dev(dev);
	if (!tb[IFLA_MTU])
		dev->mtu = mtu;

	err = register_netdevice(dev);
	if (err)
		goto out;

	dev_hold(dev);
	ipgre_tunnel_link(ign, nt);

	if (IPGRE_ISER(nt))
		ipgre_er_postinit(nt);

out:
	return err;
}

static int ipgre_changelink(struct net_device *dev, struct nlattr *tb[],
			    struct nlattr *data[])
{
	struct ip_tunnel *t, *nt;
	struct net *net = dev_net(dev);
	struct ipgre_net *ign = net_generic(net, ipgre_net_id);
	struct ip_tunnel_parm p;
	int mtu;

	if (dev == ign->fb_tunnel_dev)
		return -EINVAL;

	nt = netdev_priv(dev);
	ipgre_netlink_parms(data, &p);

	t = ipgre_tunnel_locate(net, &p, 0);

	if (t) {
		if (t->dev != dev)
			return -EEXIST;
	} else {
		unsigned nflags = 0;

		t = nt;

		if (ipv4_is_multicast(p.iph.daddr))
			nflags = IFF_BROADCAST;
		else if (p.iph.daddr)
			nflags = IFF_POINTOPOINT;

		if ((dev->flags ^ nflags) &
		    (IFF_POINTOPOINT | IFF_BROADCAST))
			return -EINVAL;

		ipgre_tunnel_unlink(ign, t);
		t->parms.iph.saddr = p.iph.saddr;
		t->parms.iph.daddr = p.iph.daddr;
		t->parms.i_key = p.i_key;
		memcpy(dev->dev_addr, &p.iph.saddr, 4);
		memcpy(dev->broadcast, &p.iph.daddr, 4);
		ipgre_tunnel_link(ign, t);
		netdev_state_change(dev);
	}

	t->parms.o_key = p.o_key;
	t->parms.iph.ttl = p.iph.ttl;
	t->parms.iph.tos = p.iph.tos;
	t->parms.iph.frag_off = p.iph.frag_off;

	if (t->parms.link != p.link) {
		t->parms.link = p.link;
		mtu = ipgre_tunnel_bind_dev(dev);
		if (!tb[IFLA_MTU])
			dev->mtu = mtu;
		netdev_state_change(dev);
	}

	return 0;
}

static size_t ipgre_get_size(const struct net_device *dev)
{
	return
		/* IFLA_GRE_LINK */
		nla_total_size(4) +
		/* IFLA_GRE_IFLAGS */
		nla_total_size(2) +
		/* IFLA_GRE_OFLAGS */
		nla_total_size(2) +
		/* IFLA_GRE_IKEY */
		nla_total_size(4) +
		/* IFLA_GRE_OKEY */
		nla_total_size(4) +
		/* IFLA_GRE_LOCAL */
		nla_total_size(4) +
		/* IFLA_GRE_REMOTE */
		nla_total_size(4) +
		/* IFLA_GRE_TTL */
		nla_total_size(1) +
		/* IFLA_GRE_TOS */
		nla_total_size(1) +
		/* IFLA_GRE_PMTUDISC */
		nla_total_size(1) +
		0;
}

static int ipgre_fill_info(struct sk_buff *skb, const struct net_device *dev)
{
	struct ip_tunnel *t = netdev_priv(dev);
	struct ip_tunnel_parm *p = &t->parms;

	NLA_PUT_U32(skb, IFLA_GRE_LINK, p->link);
	NLA_PUT_BE16(skb, IFLA_GRE_IFLAGS, p->i_flags);
	NLA_PUT_BE16(skb, IFLA_GRE_OFLAGS, p->o_flags);
	NLA_PUT_BE32(skb, IFLA_GRE_IKEY, p->i_key);
	NLA_PUT_BE32(skb, IFLA_GRE_OKEY, p->o_key);
	NLA_PUT_BE32(skb, IFLA_GRE_LOCAL, p->iph.saddr);
	NLA_PUT_BE32(skb, IFLA_GRE_REMOTE, p->iph.daddr);
	NLA_PUT_U8(skb, IFLA_GRE_TTL, p->iph.ttl);
	NLA_PUT_U8(skb, IFLA_GRE_TOS, p->iph.tos);
	NLA_PUT_U8(skb, IFLA_GRE_PMTUDISC, !!(p->iph.frag_off & htons(IP_DF)));

	return 0;

nla_put_failure:
	return -EMSGSIZE;
}

static const struct nla_policy ipgre_policy[IFLA_GRE_MAX + 1] = {
	[IFLA_GRE_LINK]		= { .type = NLA_U32 },
	[IFLA_GRE_IFLAGS]	= { .type = NLA_U16 },
	[IFLA_GRE_OFLAGS]	= { .type = NLA_U16 },
	[IFLA_GRE_IKEY]		= { .type = NLA_U32 },
	[IFLA_GRE_OKEY]		= { .type = NLA_U32 },
	[IFLA_GRE_LOCAL]	= { .len = FIELD_SIZEOF(struct iphdr, saddr) },
	[IFLA_GRE_REMOTE]	= { .len = FIELD_SIZEOF(struct iphdr, daddr) },
	[IFLA_GRE_TTL]		= { .type = NLA_U8 },
	[IFLA_GRE_TOS]		= { .type = NLA_U8 },
	[IFLA_GRE_PMTUDISC]	= { .type = NLA_U8 },
};

static struct rtnl_link_ops ipgre_link_ops __read_mostly = {
	.kind		= "gre",
	.maxtype	= IFLA_GRE_MAX,
	.policy		= ipgre_policy,
	.priv_size	= sizeof(struct ip_tunnel),
	.setup		= ipgre_tunnel_setup,
	.validate	= ipgre_tunnel_validate,
	.newlink	= ipgre_newlink,
	.changelink	= ipgre_changelink,
	.get_size	= ipgre_get_size,
	.fill_info	= ipgre_fill_info,
};

static struct rtnl_link_ops ipgre_tap_ops __read_mostly = {
	.kind		= "gretap",
	.maxtype	= IFLA_GRE_MAX,
	.policy		= ipgre_policy,
	.priv_size	= sizeof(struct ip_tunnel),
	.setup		= ipgre_tap_setup,
	.validate	= ipgre_tap_validate,
	.newlink	= ipgre_newlink,
	.changelink	= ipgre_changelink,
	.get_size	= ipgre_get_size,
	.fill_info	= ipgre_fill_info,
};

/*
 * Ethernet Relay over GRE.
 */
#define ER_TUNNEL(iptunnel)	(struct er_tunnel *)((iptunnel) + 1)
#define IP_TUNNEL(ertunnel)	((struct ip_tunnel *)(ertunnel) - 1)

#define ER_ANNOUNCE_TIME	(5 * HZ)
#define ER_EXPIRE_TIME		(5 * ER_ANNOUNCE_TIME)

struct er_vlan {
	struct er_tunnel *	vl_tun;
	struct rb_node		vl_node;
	int			vl_id;
	struct rb_root		vl_src;
	int			vl_nsrc;
	struct rb_root		vl_dst;
};

struct er_iface {
	struct rb_node		if_node;
	int			if_id;
	struct net_device *	if_dev;
	__be32			if_daddr;
	struct packet_type	if_pack;
	unsigned long		if_expire;
};

struct er_sre {
	__be16			sre_af;
	__be16			sre_len;
};

static int  ipgre_er_iface_add_src(struct er_tunnel *, struct net_device *);
static void ipgre_er_iface_del_src(struct er_tunnel *, struct net_device *);

static struct er_vlan *ipgre_er_vlan_lookup(struct er_tunnel *, int);
static struct er_vlan *ipgre_er_vlan_create(struct er_tunnel *, int);
static void ipgre_er_vlan_destroy(struct er_tunnel *, struct er_vlan *);
static void ipgre_er_vlan_insert(struct er_tunnel *, struct er_vlan *);
static int  ipgre_er_vlan_join(struct er_tunnel *, struct er_vlan *);
static void ipgre_er_vlan_leave(struct er_tunnel *, struct er_vlan *);

static struct er_iface *ipgre_er_iface_lookup(struct rb_root *, int);
static struct er_iface *ipgre_er_iface_create(struct rb_root *, int);
static void ipgre_er_iface_destroy(struct rb_root *, struct er_iface *);
static void ipgre_er_iface_insert(struct rb_root *, struct er_iface *);

static void ipgre_er_announce(struct er_tunnel *, struct er_vlan *);
static void ipgre_er_timer(unsigned long);

static int ipgre_er_mac_addr(struct net_device *, void *);
static int ipgre_er_ioctl(struct net_device *, struct ifreq *, int);
static int ipgre_er_brctl(struct er_tunnel *, int, int);
static int ipgre_er_rcv(struct sk_buff *, struct net_device *,
    struct packet_type *, struct net_device *);

static ssize_t ipgre_er_show(struct device *, struct device_attribute *,
    char *);

static const struct device_attribute ipgre_er_attr = {
	.attr = { .name = "etherelay", .mode = 0444, .owner = THIS_MODULE },
	.show = ipgre_er_show
};

static inline int
ipgre_er_vlid(unsigned char *addr)
{
	return ((addr[3] << 7) | (addr[4] >> 1));
}

static inline int
ipgre_er_ifid(unsigned char *addr)
{
	return ((addr[4] & 0x01) << 8 | addr[5]);
}

static inline __be32
ipgre_er_vtog(int vlid)
{
	return htonl(0xefff0000 + vlid);
}

static inline int
ipgre_er_gtov(__be32 group)
{
	return (ntohl(group) & 0xffff);
}

static int
ipgre_er_init(struct ip_tunnel *tunnel)
{
	struct net_device *dev = tunnel->dev;
	struct er_tunnel *ertunnel = ER_TUNNEL(tunnel);

	dev->do_ioctl = ipgre_er_ioctl;
	dev->set_mac_address = ipgre_er_mac_addr;

	ertunnel->er_vlans = RB_ROOT;
	ipgre_er_iface_add_src(ertunnel, dev);

	setup_timer(&ertunnel->er_timer, ipgre_er_timer,
	    (unsigned long)ertunnel);
	mod_timer(&ertunnel->er_timer, jiffies + ER_ANNOUNCE_TIME);

	return 0;
}

static int
ipgre_er_postinit(struct ip_tunnel *tunnel)
{
	struct net_device *dev = tunnel->dev;

	return sysfs_create_file(&dev->dev.kobj, &ipgre_er_attr.attr);
}

static void
ipgre_er_uninit(struct ip_tunnel *tunnel)
{
	struct er_tunnel *ertunnel = ER_TUNNEL(tunnel);
	struct er_vlan *vlan;
	struct rb_node *p;

	sysfs_remove_file(&tunnel->dev->dev.kobj, &ipgre_er_attr.attr);

	del_timer(&ertunnel->er_timer);

	while ((p = rb_first(&ertunnel->er_vlans))) {
		vlan = rb_entry(p, struct er_vlan, vl_node);
		ipgre_er_vlan_destroy(ertunnel, vlan);
	}
}

static void
ipgre_er_routing(struct ip_tunnel *tunnel, struct sk_buff *skb)
{
	struct er_tunnel *ertunnel = ER_TUNNEL(tunnel);
	struct iphdr *iph = ip_hdr(skb);
	struct er_sre *sre = (struct er_sre *)skb->data;
	struct er_vlan *vlan;
	__be32 daddr = iph->saddr;
	char *haddr;
	int len, vlid;

	if (skb->len < sizeof(*sre))
		return;
	if (sre->sre_af != __constant_htons(ETH_P_TEB))
		return;
	len = ntohs(sre->sre_len);
	if (skb->len != sizeof(*sre) + len)
		return;
	if (len < ETH_ALEN || len % ETH_ALEN)
		return;

	if (daddr == tunnel->parms.iph.saddr)
		/* multicast loop */
		return;

	haddr = (char *)(sre + 1);
	vlid = ipgre_er_vlid(haddr);

	write_lock(&ipgre_lock);
	if ((vlan = ipgre_er_vlan_lookup(ertunnel, vlid)) == NULL) {
		write_unlock(&ipgre_lock);
		return;
	}

	for (; len >= ETH_ALEN; len -= ETH_ALEN, haddr += ETH_ALEN) {
		struct er_iface *iface;
		int ifid;

		ifid = ipgre_er_ifid(haddr);
		if ((iface = ipgre_er_iface_lookup(&vlan->vl_dst, ifid))) {
			iface->if_daddr = daddr;
			iface->if_expire = jiffies + ER_EXPIRE_TIME;
			continue;
		}

		iface = ipgre_er_iface_create(&vlan->vl_dst, ifid);
		if (IS_ERR(iface)) {
			write_unlock(&ipgre_lock);
			return;
		}
		iface->if_daddr = daddr;
		iface->if_expire = jiffies + ER_EXPIRE_TIME;
	}
	write_unlock(&ipgre_lock);
}

static void
ipgre_er_xmit(struct ip_tunnel *tunnel, struct sk_buff *skb, __be32 daddr)
{
	struct er_tunnel *ertunnel = ER_TUNNEL(tunnel);
	struct ethhdr *eh = eth_hdr(skb);
	struct sk_buff *skb2;
	struct er_vlan *vlan;
	struct er_iface *iface;
	int vlid, ifid;

	if (is_multicast_ether_addr(eh->h_dest))
		vlid = ipgre_er_gtov(daddr);
	else
		vlid = ipgre_er_vlid(eh->h_dest);
	if ((vlan = ipgre_er_vlan_lookup(ertunnel, vlid)) == NULL)
		return;

	if (is_multicast_ether_addr(eh->h_dest)) {
		struct rb_node *p;

		for (p = rb_first(&vlan->vl_src); p; p = rb_next(p)) {
			iface = rb_entry(p, struct er_iface, if_node);
			if (iface->if_dev == tunnel->dev)
				continue;
			if ((skb2 = skb_clone(skb, GFP_ATOMIC))) {
				skb2->dev = iface->if_dev;
				skb_push(skb2, ETH_HLEN);
				dev_queue_xmit(skb2);
			}
		}
		return;
	}

	if (ipgre_er_vlid(eh->h_dest) != vlid)
		return;

	ifid = ipgre_er_ifid(eh->h_dest);
	if ((iface = ipgre_er_iface_lookup(&vlan->vl_src, ifid)) == NULL ||
	    iface->if_dev == tunnel->dev)
		return;

	if ((skb2 = skb_clone(skb, GFP_ATOMIC))) {
		skb2->dev = iface->if_dev;
		skb_push(skb2, ETH_HLEN);
		dev_queue_xmit(skb2);
	}
}

static __be32
ipgre_er_dst(struct ip_tunnel *tunnel, struct sk_buff *skb)
{
	struct er_tunnel *ertunnel = ER_TUNNEL(tunnel);
	struct ethhdr *eh = eth_hdr(skb);
	struct er_vlan *vlan;
	struct er_iface *iface;
	int vlid, ifid;

	vlid = ipgre_er_vlid(eh->h_source);
	if ((vlan = ipgre_er_vlan_lookup(ertunnel, vlid)) == NULL) {
		vlan = ertunnel->er_defvlan;
		vlid = vlan->vl_id;
	}

	if (is_multicast_ether_addr(eh->h_dest))
		return ipgre_er_vtog(vlid);

	if (ipgre_er_vlid(eh->h_dest) != vlid)
		return 0;

	ifid = ipgre_er_ifid(eh->h_dest);
	if ((iface = ipgre_er_iface_lookup(&vlan->vl_dst, ifid)))
		return iface->if_daddr;

	return 0;
}

static int
ipgre_er_iface_add_src(struct er_tunnel *ertunnel, struct net_device *dev)
{
	struct ip_tunnel *tunnel = IP_TUNNEL(ertunnel);
	struct er_vlan *vlan;
	struct er_iface *iface;
	int vlid = ipgre_er_vlid(dev->dev_addr);
	int ifid = ipgre_er_ifid(dev->dev_addr);

	mutex_lock(&ipgre_mtx);
	if ((vlan = ipgre_er_vlan_lookup(ertunnel, vlid)) == NULL)
		vlan = ipgre_er_vlan_create(ertunnel, vlid);
	if (IS_ERR(vlan)) {
		mutex_unlock(&ipgre_mtx);
		return PTR_ERR(vlan);
	}

	if (dev == tunnel->dev)
		ertunnel->er_defvlan = vlan;

	if ((ipgre_er_iface_lookup(&vlan->vl_src, ifid))) {
		mutex_unlock(&ipgre_mtx);
		return -EEXIST;
	}

	iface = ipgre_er_iface_create(&vlan->vl_src, ifid);
	if (IS_ERR(iface)) {
		mutex_unlock(&ipgre_mtx);
		return PTR_ERR(iface);
	}
	iface->if_dev = dev;

	if (dev != tunnel->dev) {
		iface->if_pack.type = __constant_htons(ETH_P_ALL);
		iface->if_pack.dev = dev;
		iface->if_pack.func = ipgre_er_rcv;
		iface->if_pack.af_packet_priv = vlan;
		dev_add_pack(&iface->if_pack);
	}

	vlan->vl_nsrc++;
	ipgre_er_announce(ertunnel, vlan);
	mutex_unlock(&ipgre_mtx);

	return 0;
}

static void
ipgre_er_iface_del_src(struct er_tunnel *ertunnel, struct net_device *dev)
{
	struct er_vlan *vlan;
	struct er_iface *iface;
	int vlid = ipgre_er_vlid(dev->dev_addr);
	int ifid = ipgre_er_ifid(dev->dev_addr);

	mutex_lock(&ipgre_mtx);
	if ((vlan = ipgre_er_vlan_lookup(ertunnel, vlid)) == NULL) {
		mutex_unlock(&ipgre_mtx);
		return;
	}

	if ((iface = ipgre_er_iface_lookup(&vlan->vl_src, ifid)) == NULL) {
		mutex_unlock(&ipgre_mtx);
		return;
	}

	ipgre_er_iface_destroy(&vlan->vl_src, iface);
	if (--vlan->vl_nsrc == 0)
		ipgre_er_vlan_destroy(ertunnel, vlan);
	mutex_unlock(&ipgre_mtx);
}

static struct er_vlan *
ipgre_er_vlan_lookup(struct er_tunnel *ertunnel, int id)
{
	struct rb_node *parent = ertunnel->er_vlans.rb_node;
	struct er_vlan *vlan;

	while (parent) {
		vlan = rb_entry(parent, struct er_vlan, vl_node);
		if (vlan->vl_id < id)
			parent = parent->rb_left;
		else if (vlan->vl_id > id)
			parent = parent->rb_right;
		else
			return vlan;
	}

	return NULL;
}

static struct er_vlan *
ipgre_er_vlan_create(struct er_tunnel *ertunnel, int id)
{
	struct er_vlan *vlan;
	int error;

	if ((vlan = kzalloc(sizeof(*vlan), GFP_KERNEL)) == NULL)
		return ERR_PTR(-ENOMEM);
	vlan->vl_tun = ertunnel;
	vlan->vl_id = id;
	vlan->vl_src = RB_ROOT;
	vlan->vl_dst = RB_ROOT;

	if ((error = ipgre_er_vlan_join(ertunnel, vlan))) {
		kfree(vlan);
		return ERR_PTR(error);
	}

	ipgre_er_vlan_insert(ertunnel, vlan);

	return vlan;
}

static void
ipgre_er_vlan_destroy(struct er_tunnel *ertunnel, struct er_vlan *vlan)
{
	struct er_iface *iface;
	struct rb_node *p;

	while ((p = rb_first(&vlan->vl_src))) {
		iface = rb_entry(p, struct er_iface, if_node);
		ipgre_er_iface_destroy(&vlan->vl_src, iface);
	}
	while ((p = rb_first(&vlan->vl_dst))) {
		iface = rb_entry(p, struct er_iface, if_node);
		ipgre_er_iface_destroy(&vlan->vl_dst, iface);
	}

	rb_erase(&vlan->vl_node, &ertunnel->er_vlans);
	ipgre_er_vlan_leave(ertunnel, vlan);
	kfree(vlan);
}

static void
ipgre_er_vlan_insert(struct er_tunnel *ertunnel, struct er_vlan *new)
{
	struct rb_node *parent = NULL, **p = &ertunnel->er_vlans.rb_node;
	struct er_vlan *vlan;

	while (*p) {
		parent = *p;
		vlan = rb_entry(parent, struct er_vlan, vl_node);
		if (vlan->vl_id < new->vl_id)
			p = &parent->rb_left;
		else if (vlan->vl_id > new->vl_id)
			p = &parent->rb_right;
	}
	rb_link_node(&new->vl_node, parent, p);
	rb_insert_color(&new->vl_node, &ertunnel->er_vlans);
}

static int
ipgre_er_vlan_join(struct er_tunnel *ertunnel, struct er_vlan *vlan)
{
	struct ip_tunnel *t = IP_TUNNEL(ertunnel);
	struct net_device *dev = t->dev;
	__be32 daddr = ipgre_er_vtog(vlan->vl_id);
	struct flowi fl = { .oif = t->parms.link,
			    .nl_u = { .ip4_u =
				      { .daddr = daddr,
					.saddr = t->parms.iph.saddr,
					.tos = RT_TOS(t->parms.iph.tos) } },
			    .proto = IPPROTO_GRE };
	struct rtable *rt;

	if (ip_route_output_key(dev_net(dev), &rt, &fl))
		return -EADDRNOTAVAIL;
	dev = rt->u.dst.dev;
	ip_rt_put(rt);
	if (__in_dev_get_rtnl(dev) == NULL)
		return -EADDRNOTAVAIL;
	t->mlink = dev->ifindex;
	ip_mc_inc_group(__in_dev_get_rtnl(dev), daddr);

	return 0;
}

static void
ipgre_er_vlan_leave(struct er_tunnel *ertunnel, struct er_vlan *vlan)
{
	struct ip_tunnel *t = IP_TUNNEL(ertunnel);
	struct net_device *dev = t->dev;
	__be32 daddr = ipgre_er_vtog(vlan->vl_id);
	struct in_device *in_dev;

	if ((in_dev = inetdev_by_index(dev_net(dev), t->mlink))) {
		ip_mc_dec_group(in_dev, daddr);
		in_dev_put(in_dev);
	}
}

static struct er_iface *
ipgre_er_iface_lookup(struct rb_root *root, int id)
{
	struct rb_node *parent = root->rb_node;
	struct er_iface *iface;

	while (parent) {
		iface = rb_entry(parent, struct er_iface, if_node);
		if (iface->if_id < id)
			parent = parent->rb_left;
		else if (iface->if_id > id)
			parent = parent->rb_right;
		else
			return iface;
	}

	return NULL;
}

static struct er_iface *
ipgre_er_iface_create(struct rb_root *root, int id)
{
	struct er_iface *iface;

	if ((iface = kzalloc(sizeof(*iface), GFP_KERNEL)) == NULL)
		return ERR_PTR(-ENOMEM);
	iface->if_id = id;

	ipgre_er_iface_insert(root, iface);

	return iface;
}

static void
ipgre_er_iface_destroy(struct rb_root *root, struct er_iface *iface)
{
	if (iface->if_pack.dev)
		dev_remove_pack(&iface->if_pack);
	rb_erase(&iface->if_node, root);
	kfree(iface);
}

static void
ipgre_er_iface_insert(struct rb_root *root, struct er_iface *new)
{
	struct rb_node *parent = NULL, **p = &root->rb_node;
	struct er_iface *iface;

	while (*p) {
		parent = *p;
		iface = rb_entry(parent, struct er_iface, if_node);
		if (iface->if_id < new->if_id)
			p = &parent->rb_left;
		else if (iface->if_id > new->if_id)
			p = &parent->rb_right;
	}
	rb_link_node(&new->if_node, parent, p);
	rb_insert_color(&new->if_node, root);
}

static void
ipgre_er_announce(struct er_tunnel *ertunnel, struct er_vlan *vlan)
{
	struct ip_tunnel *tunnel = IP_TUNNEL(ertunnel);
	__be32 daddr = ipgre_er_vtog(vlan->vl_id);
	struct flowi fl = { .oif = tunnel->parms.link,
			    .nl_u = { .ip4_u =
				      { .daddr = daddr,
					.saddr = tunnel->parms.iph.saddr } },
			    .proto = IPPROTO_GRE };
	struct rtable *rt;
	struct net_device *dev;
	struct sk_buff *skb;
	struct iphdr  *iph;
	struct er_sre *sre;
	char *addr;
	struct rb_node *p;
	int gre_flags, gre_hlen, sre_len;

	if (ip_route_output_key(dev_net(tunnel->dev), &rt, &fl))
		return;
	dev = rt->u.dst.dev;

	gre_flags = tunnel->parms.o_flags | GRE_ROUTING;
	gre_hlen = tunnel->hlen;
	if (!(gre_flags & GRE_CSUM)) {
		gre_flags |= GRE_CSUM;
		gre_hlen += 4;
	}
	sre_len = sizeof(struct er_sre) + vlan->vl_nsrc * ETH_ALEN;
	if ((skb = alloc_skb(gre_hlen + sre_len + LL_ALLOCATED_SPACE(dev),
	    GFP_ATOMIC)) == NULL) {
		ip_rt_put(rt);
		return;
	}

	skb->dst = &rt->u.dst;

	skb_reserve(skb, LL_RESERVED_SPACE(dev));

	skb_reset_network_header(skb);
	iph = ip_hdr(skb);
	skb_put(skb, gre_hlen);

	iph->version = 4;
	iph->ihl = sizeof(struct iphdr) >> 2;
	iph->tos = 0;
	iph->frag_off = __constant_htons(IP_DF);
	if ((iph->ttl = tunnel->parms.iph.ttl) == 0)
		iph->ttl = 1;
	iph->daddr = rt->rt_dst;
	iph->saddr = rt->rt_src;
	iph->protocol = IPPROTO_GRE;
	ip_select_ident(iph, &rt->u.dst, NULL);

	sre = (struct er_sre *)skb_put(skb, sre_len);
	sre->sre_af = __constant_htons(ETH_P_TEB);
	sre->sre_len = htons(vlan->vl_nsrc * ETH_ALEN);
	addr = (char *)(sre + 1);
	for (p = rb_first(&vlan->vl_src); p; p = rb_next(p)) {
		struct er_iface *iface;

		iface = rb_entry(p, struct er_iface, if_node);
		memcpy(addr, iface->if_dev->dev_addr, ETH_ALEN);
		addr += 6;
	}

	((__be16 *)(iph + 1))[0] = gre_flags;
	((__be16 *)(iph + 1))[1] = __constant_htons(ETH_P_TEB);

	if (gre_flags & (GRE_KEY | GRE_CSUM | GRE_SEQ)) {
		__be32 *ptr = (__be32 *)(((u8 *)iph) + gre_hlen - 4);

		if (gre_flags & GRE_SEQ) {
			++tunnel->o_seqno;
			*ptr = htonl(tunnel->o_seqno);
			ptr--;
		}
		if (gre_flags & GRE_KEY) {
			*ptr = tunnel->parms.o_key;
			ptr--;
		}
		if (gre_flags & GRE_CSUM) {
			*ptr = 0;
			*(__sum16 *)ptr = ip_compute_csum((void *)(iph + 1),
			    skb->len - sizeof(struct iphdr));
		}
	}

	ip_local_out(skb);
}

static void
ipgre_er_timer(unsigned long data)
{
	struct er_tunnel *ertunnel = (struct er_tunnel *)data;
	struct ip_tunnel *tunnel = IP_TUNNEL(ertunnel);
	struct er_vlan *vlan;
	struct er_iface *iface;
	struct rb_node *p, *pp;

	if (!(tunnel->dev->flags & IFF_UP))
		goto done;

	write_lock(&ipgre_lock);
	for (p = rb_first(&ertunnel->er_vlans); p; p = rb_next(p)) {
		vlan = rb_entry(p, struct er_vlan, vl_node);
		ipgre_er_announce(ertunnel, vlan);

		for (pp = rb_first(&vlan->vl_dst); pp; pp = rb_next(pp)) {
			iface = rb_entry(pp, struct er_iface, if_node);
			if (time_after(jiffies, iface->if_expire))
				ipgre_er_iface_destroy(&vlan->vl_dst, iface);
		}
	}
	write_unlock(&ipgre_lock);

done:
	mod_timer(&ertunnel->er_timer, jiffies + ER_ANNOUNCE_TIME);
}

static int
ipgre_er_mac_addr(struct net_device *dev, void *p)
{
	struct ip_tunnel *tunnel = netdev_priv(dev);
	struct er_tunnel *ertunnel = ER_TUNNEL(tunnel);
	struct sockaddr *addr = p;

	if (netif_running(dev))
		return -EBUSY;
	if (!is_valid_ether_addr(addr->sa_data))
		return -EADDRNOTAVAIL;

	ipgre_er_iface_del_src(ertunnel, dev);
	memcpy(dev->dev_addr, addr->sa_data, ETH_ALEN);
	return ipgre_er_iface_add_src(ertunnel, dev);
}

static int
ipgre_er_ioctl(struct net_device *dev, struct ifreq *ifr, int cmd)
{
	struct ip_tunnel *tunnel = netdev_priv(dev);
	struct er_tunnel *ertunnel = ER_TUNNEL(tunnel);

	switch (cmd) {
	case SIOCBRADDIF:
	case SIOCBRDELIF:
		return ipgre_er_brctl(ertunnel, ifr->ifr_ifindex,
		    cmd == SIOCBRADDIF);
	}

	return -EOPNOTSUPP;
}

static int
ipgre_er_brctl(struct er_tunnel *ertunnel, int ifindex, int isadd)
{
	struct net_device *dev;
	int ret = 0;

	if (!capable(CAP_NET_ADMIN))
		return -EPERM;

	dev = dev_get_by_index(&init_net, ifindex);
	if (dev == NULL)
		return -EINVAL;

	if (isadd)
		ret = ipgre_er_iface_add_src(ertunnel, dev);
	else
		ipgre_er_iface_del_src(ertunnel, dev);

	dev_put(dev);
	return ret;
}

static int
ipgre_er_rcv(struct sk_buff *skb, struct net_device *dev,
    struct packet_type *pack, struct net_device *orig_dev)
{
	struct er_vlan *vlan = pack->af_packet_priv;
	struct er_tunnel *ertunnel = vlan->vl_tun;
	struct ip_tunnel *tunnel = IP_TUNNEL(ertunnel);
	struct er_iface *iface;
	struct ethhdr *eh;

	if (skb->pkt_type == PACKET_OUTGOING)
		goto drop;

	if ((skb = skb_share_check(skb, GFP_ATOMIC)) == NULL)
		goto drop;

	skb_push(skb, ETH_HLEN);
	eh = eth_hdr(skb);

	if (ipgre_er_vlid(eh->h_source) != vlan->vl_id)
		goto drop;

	if (is_multicast_ether_addr(eh->h_dest)) {
		struct rb_node *p;
		struct sk_buff *skb2;

		for (p = rb_first(&vlan->vl_src); p; p = rb_next(p)) {
			iface = rb_entry(p, struct er_iface, if_node);
			if (iface->if_dev == dev ||
			    iface->if_dev == tunnel->dev)
				continue;
			if ((skb2 = skb_clone(skb, GFP_ATOMIC))) {
				skb2->dev = iface->if_dev;
				dev_queue_xmit(skb2);
			}
		}

		skb->dev = tunnel->dev;
		dev_queue_xmit(skb);
		return 0;
	}

	if ((iface = ipgre_er_iface_lookup(&vlan->vl_src,
	    ipgre_er_ifid(eh->h_dest)))) {
		if (iface->if_dev == dev)
			goto drop;
		skb->dev = iface->if_dev;
	} else {
		skb->dev = tunnel->dev;
	}

	dev_queue_xmit(skb);
	return 0;

drop:
	kfree_skb(skb);
	return NET_RX_DROP;
}

static ssize_t
ipgre_er_show(struct device *d, struct device_attribute *attr, char *buf)
{
	struct net_device *dev = container_of(d, struct net_device, dev);
	struct ip_tunnel *tunnel = netdev_priv(dev);
	struct er_tunnel *ertunnel = ER_TUNNEL(tunnel);
	struct er_vlan *vlan;
	struct er_iface *iface;
	struct rb_node *p, *pp;
	ssize_t count = 0;

	read_lock_bh(&ipgre_lock);
	for (p = rb_first(&ertunnel->er_vlans); p; p = rb_next(p)) {
		vlan = rb_entry(p, struct er_vlan, vl_node);
		count += sprintf(buf + count, "vlan %d\n", vlan->vl_id);

		for (pp = rb_first(&vlan->vl_src); pp; pp = rb_next(pp)) {
			iface = rb_entry(pp, struct er_iface, if_node);
			count += sprintf(buf + count, " %s",
			    iface->if_dev->name);
		}
		count += sprintf(buf + count, "\n");

		for (pp = rb_first(&vlan->vl_dst); pp; pp = rb_next(pp)) {
			unsigned char *a;

			iface = rb_entry(pp, struct er_iface, if_node);
			a = (unsigned char *)&iface->if_daddr;
			count += sprintf(buf + count, " %d %d.%d.%d.%d\n",
			    iface->if_id, a[0], a[1], a[2], a[3]);
		}

	}
	read_unlock_bh(&ipgre_lock);

	return count;
}

/*
 *	And now the modules code and kernel interface.
 */

static int __init ipgre_init(void)
{
	int err;

	printk(KERN_INFO "GRE over IPv4 tunneling driver\n");

	if (inet_add_protocol(&ipgre_protocol, IPPROTO_GRE) < 0) {
		printk(KERN_INFO "ipgre init: can't add protocol\n");
		return -EAGAIN;
	}

	err = register_pernet_gen_device(&ipgre_net_id, &ipgre_net_ops);
	if (err < 0)
		goto gen_device_failed;

	err = rtnl_link_register(&ipgre_link_ops);
	if (err < 0)
		goto rtnl_link_failed;

	err = rtnl_link_register(&ipgre_tap_ops);
	if (err < 0)
		goto tap_ops_failed;

out:
	return err;

tap_ops_failed:
	rtnl_link_unregister(&ipgre_link_ops);
rtnl_link_failed:
	unregister_pernet_gen_device(ipgre_net_id, &ipgre_net_ops);
gen_device_failed:
	inet_del_protocol(&ipgre_protocol, IPPROTO_GRE);
	goto out;
}

static void __exit ipgre_fini(void)
{
	rtnl_link_unregister(&ipgre_tap_ops);
	rtnl_link_unregister(&ipgre_link_ops);
	unregister_pernet_gen_device(ipgre_net_id, &ipgre_net_ops);
	if (inet_del_protocol(&ipgre_protocol, IPPROTO_GRE) < 0)
		printk(KERN_INFO "ipgre close: can't remove protocol\n");
}

module_init(ipgre_init);
module_exit(ipgre_fini);
MODULE_LICENSE("GPL");
MODULE_ALIAS_RTNL_LINK("gre");
MODULE_ALIAS_RTNL_LINK("gretap");
