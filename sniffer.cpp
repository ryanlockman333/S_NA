/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * sniffer.cpp                                                                               *
 * Description: Sniffer class implementations and miscellaneous.                             *
 * Last Update: 06/09/15                                                                     *
 * (C) Copyright - Ryan Lockman                                                                                          *
 * )))~3L1735~(((                                                                            *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

///////////////////////////////////////////////////////////////////////////////////////////////
// *TODO*
// set up new interface for rfmon(mon0) and delete it after
// parse by IGMP/ICMP/ARP opcodes
// fix printing of ICMP header unions, can only acces one at once
// add tpacket_v3
// defines for any random number values
// convert timestamps and seconds in tpacket and TSFT(mactime) radiotap
// check fanout mode and cpu affinity
// further PAE(EAPOL)
// add data-link layers PPP/FCPP and network layers PPPoE
// print App Level HTTP...
// maybe fix some -Wall, -Wextra, -pedantic-errors
// add tdls header(wifi direct)
// try WEP decrypt
// bottom is backdoor experimental
// better packet_switch
// printing of MGMT IE's, capabilities, vars/actions not checked or added
// stp flags
// ipv6 extension headers
// better sniffer initalization of data members and setting of flags
// tcp Congestion and explicit flags, tcp extensions
// defaults in control frame subtype and maybe default frame type/CTL_EXT/EXT_FRAME
// eth0 iwhmode ifctl
// qos control field bits
// HT extra addon in addr3 and addr4
// radiotap printing
// oui dictionary
// add HT ctrl field in 802.11 frame only when the order bit is set
// fix WDS not going through, in 802.11 data frame instead ETH_802
// *makepage
///////////////////////////////////////////////////////////////////////////////////////////////

// Feature Test Macros
#ifndef _BSD_SOURCE
#define _BSD_SOURCE // <endian.h>
#endif

#ifndef _GNU_SOURCE // <sched.h> sched_setaffinity
#define _GNU_SOURCE
#endif

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * " * * * * * * * * * * * * */

// Headers
#include <sstream>
#include <string>
#include <ctime>
#include <cassert>
#include <iomanip>
#include <iostream>
#include <csignal>
#include <cerrno>
#include <cstdio>

#include <fcntl.h>
#include <endian.h>
#include <poll.h>
#include <sched.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <sys/socket.h>

#include <netinet/ip_icmp.h>
#include <netinet/udp.h>
#include <netinet/tcp.h>
#include <netinet/sctp.h>
#include <netinet/ip.h>
#include <netinet/ether.h>
#include <net/if_arp.h> // linux/if_arp conflicts with net/if_arp
#include <linux/igmp.h>
#include <linux/filter.h>
#include <linux/net_tstamp.h>
#include <linux/if.h>
#include <linux/if_tun.h>
//#include <linux/in6.h>  // causes conficts with netinet/ip_icmp and netinet/in
//#include <linux/ipv6.h> // causes conficts with netinet/ip_icmp and netinet/in

#include "sniffer.h" // local

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// WEP Decrypting Stuff
// RC4 State
typedef struct {
	u_char	perm[256]; // premutation
	u_char	index1;    // idx1
	u_char	index2;    // idx2
} rc4_state;

// Swap Bytes
static __inline void swap_bytes(u_char *a, u_char *b) {
	u_char temp_a = *a;
	*a = *b;
	*b = temp_a;
}

// RC4 Initialization
void rc4_init(rc4_state *const state, const u_char *key, int keylen) {
	// Declarations
	int i = 0;

	// Initialize State With Identity Permutation
	for(i = 0; i < 256; ++i)
		state->perm[i] = (u_char)i;

	state->index1 = 0;
	state->index2 = 0;
  
	// Randomize The Permutation Using Key Data
	for(u_char j = i = 0; i < 256; ++i) {
		j += state->perm[i] + key[i % keylen]; 
		swap_bytes(&state->perm[i], &state->perm[j]);
	}
}

// RC4 Stream Cypher, Encryption And Decryption Function
void rc4_crypt(rc4_state *const state, const u_char *inbuf, u_char *outbuf, int buflen) {
	u_char j = 0;

	for(int i = 0; i < buflen; ++i) {
		// Update Modification Indicies
		++state->index1;
		state->index2 += state->perm[state->index1];

		// Modify Permutation
		swap_bytes(&state->perm[state->index1], &state->perm[state->index2]);

		// Encrypt/Decrypt Next Byte
		j         = state->perm[state->index1] + state->perm[state->index2];
		outbuf[i] = inbuf[i] ^ state->perm[j];
	}
}

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// ANSI Excape Macros
#define RED     "\033[1;31m"
#define GREEN   "\033[1;32m"
#define YELLOW  "\033[1;33m"
#define NF      "\033[0m"
#define CLRLN   "\033[2K"
#define CUP     "\033[1A"
#define CLRSCRN "\033[2J" \
                "\033[1;1H"

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// Incase glibc 2.1
#ifndef SOL_PACKET
#define SOL_PACKET 263
#endif

// TPacket Defines
#ifndef TP_STATUS_VLAN_TPID_VALID
#define TP_STATUS_VLAN_TPID_VALID (1 << 6)
#endif

// Ethernet Defines, Not Always Included (ether_types)
#ifndef ETH_P_BATMAN
#define ETH_P_BATMAN    0x4305
#endif
#ifndef ETH_P_MVRP
#define ETH_P_MVRP      0x88F5
#endif
#ifndef ETH_P_PRP
#define ETH_P_PRP       0x88FB
#endif
#ifndef ETH_P_80221
#define ETH_P_80221     0x8917
#endif
#ifndef ETH_P_LOOPBACK
#define ETH_P_LOOPBACK  0x9000
#endif
#ifndef ETH_P_802_3_MIN
#define ETH_P_802_3_MIN 0x0600
#endif

// Expirimental Ethernets
#define ETH_P_ROOFNET1  0x0641
#define ETH_P_ROOFNET3  0x0643
#define ETH_P_ROOFNET4  0x0644
#define ETH_P_ROOFNET5  0x0645

// ARP Defines, Not Always Included
#ifndef ARPHRD_CAN
#define ARPHRD_CAN                280
#endif
#define ARPHRD_IEEE802154_MONITOR 805
#ifndef ARPHRD_PHONET
#define ARPHRD_PHONET             820
#endif
#ifndef ARPHRD_PHONET_PIPE
#define ARPHRD_PHONET_PIPE        821
#endif
#ifndef ARPHRD_CAIF
#define ARPHRD_CAIF               822
#endif
#ifndef ARPHRD_IP6GRE
#define ARPHRD_IP6GRE             823
#endif
#ifndef ARPHRD_NETLINK
#define ARPHRD_NETLINK            824
#endif
#ifndef ARPHRD_6LOWPAN
#define ARPHRD_6LOWPAN            825
#endif

// IP Defines, Not Always Included
#ifndef IPPROTO_BEETPH
#define IPPROTO_BEETPH 94
#endif

// IP Version Defines And IPv6 Flow Lable Length
#define IPV4 4
#define IPV6 6
#define IPV6_FLOW_LBL_LEN 3

// IPv6 Next Header Field Extensions(Upper Protocols), actually in linux/in6.h but conflicts
#ifndef IPPROTO_HOPOPTS
#define IPPROTO_HOPOPTS   0 // hop-by-hop options
#endif
#ifndef IPPROTO_ROUTING
#define IPPROTO_ROUTING  43 // routing header
#endif
#ifndef IPPROTO_FRAGMENT
#define IPPROTO_FRAGMENT 44 // fragmentation header
#endif
#ifndef IPPROTO_ICMPV6
#define IPPROTO_ICMPV6   58 // ICMPv6
#endif
#ifndef IPPROTO_NONE
#define IPPROTO_NONE     59 // no next header(no upper protocols)
#endif
#ifndef IPPROTO_DSTOPTS
#define IPPROTO_DSTOPTS  60 // destination options
#endif
#ifndef IPPROTO_MH
#define IPPROTO_MH      135 // mobility header
#endif

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// Packing, Alignments, Offsets, Conversion, And (Un)Likely Defines
#ifndef __packed
#define __packed           __attribute__((packed)) // pack
#endif

#ifndef __aligned
#define __aligned(x)       __attribute__((aligned(x))) // align
#endif

#ifndef __aligned_tpacket
#define __aligned_tpacket  __attribute__((aligned(TPACKET_ALIGNMENT))) // tpacket align
#endif

#ifndef __align_tpacket
#define __align_tpacket(x) __attribute__((aligned(TPACKET_ALIGN(x)))) // tpacket align x
#endif

#define PKT_OFFSET (TPACKET_ALIGN(sizeof(tpacket2_hdr)) + \
                    TPACKET_ALIGN(sizeof(sockaddr_ll))) // packet offset from start

#define RTAP_ALIGN_OFFSET(offset, width) \
    ((((offset) + ((width) - 1)) & (~((width) - 1))) - offset) // radiotap, next data offset


// Convert Little Endian To CPU(Host) For IEEE802.11
#define pletohs(ptr) ((unsigned short)                                 \
                     ((unsigned short)*((cuchar_cptr)(ptr) + 1) << 8 | \
                      (unsigned short)*((cuchar_cptr)(ptr) + 0) << 0))

// Convert CPU(Host) To Little Endian For IEEE802.11
#define phtoles(p, v) {                 \
    (p)[0] = (unsigned char)((v) >> 0); \
    (p)[1] = (unsigned char)((v) >> 8); \
}

// Defines For V3 Packet, Likely/Unlikely
#ifndef likely
# define likely(x)   __builtin_expect(!!(x), 1)
#endif
#ifndef unlikely
# define unlikely(x) __builtin_expect(!!(x), 0)
#endif

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// For Below
#define us unsigned short
#define BIT(x) (1 << (x)) // bitshifting

// LLC And IP Bitmask Parsing Defines
#define CHECKBIT_LLC(p, x) ((*(unsigned*)(p)) & BIT(x))
#define CHECKBIT_IP(p, x)  (ntohs(*(us*)(p))  & BIT(x))

// Spanning Tree Protocol Header, Ethernet And 802.1d And 802.1w And 802.1Q
#define GET_STP_PRIORITY(x) ((x) & (unsigned short)(0xFFFF000000000000 >> 48)
#define GET_STP_ID(x)       ((x) & 0x0000FFFFFFFFFFFF)

// ieee8022 Header And Radiotap Bit Parsing Shit Below
// Shifting And Bit Checking For Both Rtap And ieee802.11 Headers
#define CHECKBIT(p, x) (le16toh((*(us*)(p))) & BIT(x)) // check bit in little endian

// Radiotap Bitmask Defines
// Radiotap Header Bit Locations
#define _TSFT          0
#define _FLAGS         1
#define _RATE          2
#define _CHANNEL       3
#define _FHSS          4
#define _ANTSIGNAL     5
#define _ANTNOISE      6
#define _LOCKQUALITY   7
#define _TX_ATTEN      8
#define _DB_TX_ATTEN   9
#define _DBM_TXPWR    10
#define _ANTENNA      11
#define _DB_ANTSIG    12
#define _DB_ANTNOISE  13
#define _RX_FLAGS     14
#define _TX_FLAGS     15
#define _RTS_RETRIES  16
#define _DATA_RETRIES 17
#define _MCS          19
#define _AMPDU_STATS  20
#define _VHT          21
#define _RTAP_NSPACE  29 // 29 + 32*n
#define _VEND_NSPACE  30 // 30 + 32*n
#define _BITMAP_EXT   31 // 31 + 32*n

// Radiotap Present Bitmask Boolean Checks
#define _GET_TSFT(p)         (CHECKBIT(p, _TSFT))
#define _GET_FLAGS(p)        (CHECKBIT(p, _FLAGS))
#define _GET_RATE(p)         (CHECKBIT(p, _RATE))
#define _GET_CHANNEL(p)      (CHECKBIT(p, _CHANNEL))
#define _GET_FHSS(p)         (CHECKBIT(p, _FHSS))
#define _GET_ANTSIGNAL(p)    (CHECKBIT(p, _ANTSIGNAL))
#define _GET_ANTNOISE(p)     (CHECKBIT(p, _ANTNOISE))
#define _GET_LOCKQUALITY(p)  (CHECKBIT(p, _LOCKQUALITY))
#define _GET_TX_ATTEN(p)     (CHECKBIT(p, _TX_ATTEN))
#define _GET_DB_TX_ATTEN(p)  (CHECKBIT(p, _DB_TX_ATTEN))
#define _GET_DBM_TXPWR(p)    (CHECKBIT(p, _DBM_TXPWR))
#define _GET_ANTENNA(p)      (CHECKBIT(p, _ANTENNA))
#define _GET_DB_ANTSIG(p)    (CHECKBIT(p, _DB_ANTSIG))
#define _GET_DB_ANTNOISE(p)  (CHECKBIT(p, _DB_ANTNOISE))
#define _GET_RX_FLAGS(p)     (CHECKBIT(p, _RX_FLAGS))
#define _GET_TX_FLAGS(p)     (CHECKBIT(p, _TX_FLAGS))
#define _GET_RTS_RETRIES(p)  (CHECKBIT(p, _RTS_RETRIES))
#define _GET_DATA_RETRIES(p) (CHECKBIT(p, _DATA_RETRIES))
#define _GET_MCS(p)          (CHECKBIT(p, _MCS))
#define _GET_AMPDU_STATS(p)  (CHECKBIT(p, _AMPDU_STATS))
#define _GET_VHT(p)          (CHECKBIT(p, _VHT))
#define _GET_RTAP_NSPACE(p)  (CHECKBIT(p, _RTAP_NSPACE))
#define _GET_VEND_NSPACE(p)  (CHECKBIT(p, _VEND_NSPACE))
#define _GET_BITMAP_EXT(p)   (CHECKBIT(p, _BITMAP_EXT))

// Enumerations For Mostly 802.11 MGMT Frame Parameters
// Information Elements
enum ieee80211_info_elementes {
    WLAN_MGMT_IE_SSID             = 0,
    WLAN_MGMT_IE_RATES            = 1,
    WLAN_MGMT_IE_FH_PARAM         = 2,
    WLAN_MGMT_IE_DS_PARAM         = 3,
    WLAN_MGMT_IE_CF_PARAM         = 4,
    WLAN_MGMT_IE_TIM              = 5,
    WLAN_MGMT_IE_IBSS_PARAM       = 6,
    WLAN_MGMT_IE_COUNTRY          = 7,  // 802.11d
    WLAN_MGMT_IE_HOP_PARAM        = 8,  // 802.11d
    WLAN_MGMT_IE_HOP_TABLE        = 9,  // 802.11d
    WLAN_MGMT_IE_REQUEST          = 10, // 802.11d
    WLAN_MGMT_IE_QBSS_LOAD        = 11,
    WLAN_MGMT_IE_EDCA_PARAM       = 12,
    WLAN_MGMT_IE_TSPEC            = 13,
    WLAN_MGMT_IE_TCLAS            = 14,
    WLAN_MGMT_IE_SCEDULE          = 15,
    WLAN_MGMT_IE_CHALLENGE_TEXT   = 16,
    WLAN_MGMT_IE_POWER_CONSTRAINT_OLD = 32, // 802.11h
    WLAN_MGMT_IE_POWER_CAPAB      = 33,  // 802.11h
    WLAN_MGMT_IE_TPC_REQUEST      = 34,  // 802.11h
    WLAN_MGMT_IE_TPC_REPORT       = 35,  // 802.11h
    WLAN_MGMT_IE_CHANNELS         = 36,  // 802.11h
    WLAN_MGMT_IE_CHANNEL_SWITCH   = 37,  // 802.11h
    WLAN_MGMT_IE_MEASURE_REQUEST  = 38,  // 802.11h
    WLAN_MGMT_IE_MEASURE_REPORT   = 39,  // 802.11h
    WLAN_MGMT_IE_QUITE            = 40,  // 802.11h
    WLAN_MGMT_IE_IBSS_DFS         = 41,  // 802.11h
    WLAN_MGMT_IE_ERP_INFO         = 42,  // 802.11g
    WLAN_MGMT_IE_TS_DELAY         = 43,
    WLAN_MGMT_IE_TCLAS_PROCESSING = 44,
    WLAN_MGMT_IE_HT_CAPABILITY    = 45,  // 802.11n
    WLAN_MGMT_IE_QOS_CAPABILITY   = 46,
    WLAN_MGMT_IE_ERP              = 47,  // 802.11g
    WLAN_MGMT_IE_RSN              = 48,  // 802.11i
    WLAN_MGMT_IE_EXT_RATES        = 50,  // 802.11g
    WLAN_MGMT_IE_POWER_CONSTRAINT = 52,  // 802.11h
    WLAN_MGMT_IE_MOBILITY_DOMAIN  = 54,  // 802.11r
    WLAN_MGMT_IE_HT_OPERATION     = 61,  // 802.11n
    WLAN_MGMT_IE_RM_ENABLED_CAPAB = 70,
    WLAN_MGMT_IE_20_40_BSS_COEX   = 72,  // 802.11n
    WLAN_MGMT_IE_OVERLAP_BSS_SCAN = 74,  // 802.11n
    WLAN_MGMT_IE_EXT_CAPABILITY   = 127,
    WLAN_MGMT_IE_CISCO_PROPERTY   = 133, // cisco proprietary
    WLAN_MGMT_IE_CISCO_SYSTEMS    = 150, // cisco systems
    WLAN_MGMT_IE_VHT_CAPABILITY   = 191, // 802.11ac
    WLAN_MGMT_IE_VHT_OPERATION    = 192, // 802.11ac
    WLAN_MGMT_IE_VHT_TRANSMIT_PWR = 195, // 802.11ac
    WLAN_MGMT_IE_VENDOR           = 221, // vendor specific
};

// Status Codes
enum ieee80211_statuscode {
    WLAN_STATUS_SUCCESS = 0,
    WLAN_STATUS_UNSPECIFIED_FAILURE = 1,
    WLAN_STATUS_CAPS_UNSUPPORTED = 10,
    WLAN_STATUS_REASSOC_NO_ASSOC = 11,
    WLAN_STATUS_ASSOC_DENIED_UNSPEC = 12,
    WLAN_STATUS_NOT_SUPPORTED_AUTH_ALG = 13,
    WLAN_STATUS_UNKNOWN_AUTH_TRANSACTION = 14,
    WLAN_STATUS_CHALLENGE_FAIL = 15,
    WLAN_STATUS_AUTH_TIMEOUT = 16,
    WLAN_STATUS_AP_UNABLE_TO_HANDLE_NEW_STA = 17,
    WLAN_STATUS_ASSOC_DENIED_RATES = 18,
    // 802.11b
    WLAN_STATUS_ASSOC_DENIED_NOSHORTPREAMBLE = 19,
    WLAN_STATUS_ASSOC_DENIED_NOPBCC = 20,
    WLAN_STATUS_ASSOC_DENIED_NOAGILITY = 21,
    // 802.11h
    WLAN_STATUS_ASSOC_DENIED_NOSPECTRUM = 22,
    WLAN_STATUS_ASSOC_REJECTED_BAD_POWER = 23,
    WLAN_STATUS_ASSOC_REJECTED_BAD_SUPP_CHAN = 24,
    // 802.11g
    WLAN_STATUS_ASSOC_DENIED_NOSHORTTIME = 25,
    WLAN_STATUS_ASSOC_DENIED_NODSSSOFDM = 26,
    // 802.11w
    WLAN_STATUS_ASSOC_REJECTED_TEMPORARILY = 30,
    WLAN_STATUS_ROBUST_MGMT_FRAME_POLICY_VIOLATION = 31,
    // 802.11i
    WLAN_STATUS_INVALID_IE = 40,
    WLAN_STATUS_INVALID_GROUP_CIPHER = 41,
    WLAN_STATUS_INVALID_PAIRWISE_CIPHER = 42,
    WLAN_STATUS_INVALID_AKMP = 43,
    WLAN_STATUS_UNSUPP_RSN_VERSION = 44,
    WLAN_STATUS_INVALID_RSN_IE_CAP = 45,
    WLAN_STATUS_CIPHER_SUITE_REJECTED = 46,
    // 802.11e
    WLAN_STATUS_UNSPECIFIED_QOS = 32,
    WLAN_STATUS_ASSOC_DENIED_NOBANDWIDTH = 33,
    WLAN_STATUS_ASSOC_DENIED_LOWACK = 34,
    WLAN_STATUS_ASSOC_DENIED_UNSUPP_QOS = 35,
    WLAN_STATUS_REQUEST_DECLINED = 37,
    WLAN_STATUS_INVALID_QOS_PARAM = 38,
    WLAN_STATUS_CHANGE_TSPEC = 39,
    WLAN_STATUS_WAIT_TS_DELAY = 47,
    WLAN_STATUS_NO_DIRECT_LINK = 48,
    WLAN_STATUS_STA_NOT_PRESENT = 49,
    WLAN_STATUS_STA_NOT_QSTA = 50,
    // 802.11s
    WLAN_STATUS_ANTI_CLOG_REQUIRED = 76,
    WLAN_STATUS_FCG_NOT_SUPP = 78,
    WLAN_STATUS_STA_NO_TBTT = 78,
    // 802.11ad
    WLAN_STATUS_REJECTED_WITH_SUGGESTED_CHANGES = 39,
    WLAN_STATUS_REJECTED_FOR_DELAY_PERIOD = 47,
    WLAN_STATUS_REJECT_WITH_SCHEDULE = 83,
    WLAN_STATUS_PENDING_ADMITTING_FST_SESSION = 86,
    WLAN_STATUS_PERFORMING_FST_NOW = 87,
    WLAN_STATUS_PENDING_GAP_IN_BA_WINDOW = 88,
    WLAN_STATUS_REJECT_U_PID_SETTING = 89,
    WLAN_STATUS_REJECT_DSE_BAND = 96,
    WLAN_STATUS_DENIED_WITH_SUGGESTED_BAND_AND_CHANNEL = 99,
    WLAN_STATUS_DENIED_DUE_TO_SPECTRUM_MANAGEMENT = 103,
};

// Reason Codes
enum ieee80211_reasoncode {
    WLAN_REASON_UNSPECIFIED = 1,
    WLAN_REASON_PREV_AUTH_NOT_VALID = 2,
    WLAN_REASON_DEAUTH_LEAVING = 3,
    WLAN_REASON_DISASSOC_DUE_TO_INACTIVITY = 4,
    WLAN_REASON_DISASSOC_AP_BUSY = 5,
    WLAN_REASON_CLASS2_FRAME_FROM_NONAUTH_STA = 6,
    WLAN_REASON_CLASS3_FRAME_FROM_NONASSOC_STA = 7,
    WLAN_REASON_DISASSOC_STA_HAS_LEFT = 8,
    WLAN_REASON_STA_REQ_ASSOC_WITHOUT_AUTH = 9,
    // 802.11h
    WLAN_REASON_DISASSOC_BAD_POWER = 10,
    WLAN_REASON_DISASSOC_BAD_SUPP_CHAN = 11,
    // 802.11i
    WLAN_REASON_INVALID_IE = 13,
    WLAN_REASON_MIC_FAILURE = 14,
    WLAN_REASON_4WAY_HANDSHAKE_TIMEOUT = 15,
    WLAN_REASON_GROUP_KEY_HANDSHAKE_TIMEOUT = 16,
    WLAN_REASON_IE_DIFFERENT = 17,
    WLAN_REASON_INVALID_GROUP_CIPHER = 18,
    WLAN_REASON_INVALID_PAIRWISE_CIPHER = 19,
    WLAN_REASON_INVALID_AKMP = 20,
    WLAN_REASON_UNSUPP_RSN_VERSION = 21,
    WLAN_REASON_INVALID_RSN_IE_CAP = 22,
    WLAN_REASON_IEEE8021X_FAILED = 23,
    WLAN_REASON_CIPHER_SUITE_REJECTED = 24,
    // TDLS 802.11z
    WLAN_REASON_TDLS_TEARDOWN_UNREACHABLE = 25,
    WLAN_REASON_TDLS_TEARDOWN_UNSPECIFIED = 26,
    // 802.11e
    WLAN_REASON_DISASSOC_UNSPECIFIED_QOS = 32,
    WLAN_REASON_DISASSOC_QAP_NO_BANDWIDTH = 33,
    WLAN_REASON_DISASSOC_LOW_ACK = 34,
    WLAN_REASON_DISASSOC_QAP_EXCEED_TXOP = 35,
    WLAN_REASON_QSTA_LEAVE_QBSS = 36,
    WLAN_REASON_QSTA_NOT_USE = 37,
    WLAN_REASON_QSTA_REQUIRE_SETUP = 38,
    WLAN_REASON_QSTA_TIMEOUT = 39,
    WLAN_REASON_QSTA_CIPHER_NOT_SUPP = 45,
    // 802.11s
    WLAN_REASON_MESH_PEER_CANCELED = 52,
    WLAN_REASON_MESH_MAX_PEERS = 53,
    WLAN_REASON_MESH_CONFIG = 54,
    WLAN_REASON_MESH_CLOSE = 55,
    WLAN_REASON_MESH_MAX_RETRIES = 56,
    WLAN_REASON_MESH_CONFIRM_TIMEOUT = 57,
    WLAN_REASON_MESH_INVALID_GTK = 58,
    WLAN_REASON_MESH_INCONSISTENT_PARAM = 59,
    WLAN_REASON_MESH_INVALID_SECURITY = 60,
    WLAN_REASON_MESH_PATH_ERROR = 61,
    WLAN_REASON_MESH_PATH_NOFORWARD = 62,
    WLAN_REASON_MESH_PATH_DEST_UNREACHABLE = 63,
    WLAN_REASON_MAC_EXISTS_IN_MBSS = 64,
    WLAN_REASON_MESH_CHAN_REGULATORY = 65,
    WLAN_REASON_MESH_CHAN = 66,
};

// Action Categories
enum ieee80211_category {
    WLAN_CATEGORY_SPECTRUM_MGMT = 0,
    WLAN_CATEGORY_QOS = 1,
    WLAN_CATEGORY_DLS = 2,
    WLAN_CATEGORY_BACK = 3,
    WLAN_CATEGORY_PUBLIC = 4,
    WLAN_CATEGORY_RADIO_MEASUREMENT = 5,
    WLAN_CATEGORY_FAST_BSS_TRANSITION = 6,
    WLAN_CATEGORY_HT = 7, // 802.11n
    WLAN_CATEGORY_SA_QUERY = 8,
    WLAN_CATEGORY_PROTECTED_DUAL_OF_ACTION = 9,
    WLAN_CATEGORY_TDLS = 12, // 802.11z
    WLAN_CATEGORY_MESH_ACTION = 13, // 802.11s
    WLAN_CATEGORY_MULTIHOP_ACTION = 14,
    WLAN_CATEGORY_SELF_PROTECTED = 15,
    WLAN_CATEGORY_DMG = 16,
    WLAN_CATEGORY_WMM = 17,
    WLAN_CATEGORY_FST = 18,
    WLAN_CATEGORY_UNPROT_DMG = 20,
    WLAN_CATEGORY_VHT = 21, // 802.11ac
    WLAN_CATEGORY_VENDOR_SPECIFIC_PROTECTED = 126,
    WLAN_CATEGORY_VENDOR_SPECIFIC = 127,
};

// SPECTRUM_MGMT Action Codes
enum ieee80211_spectrum_mgmt_actioncode {
    WLAN_ACTION_SPCT_MSR_REQ = 0,
    WLAN_ACTION_SPCT_MSR_RPRT = 1,
    WLAN_ACTION_SPCT_TPC_REQ = 2,
    WLAN_ACTION_SPCT_TPC_RPRT = 3,
    WLAN_ACTION_SPCT_CHL_SWITCH = 4,
};

// QOS_MGMT Action Codes
enum ieee80211_qos_mgmt_actioncode {
    WLAN_ACTION_QOS_ADDTS_REQ = 0,
    WLAN_ACTION_QOS_ADDTS_RESP = 1,
    WLAN_ACTION_QOS_DELTS = 2,
    WLAN_ACTION_QOS_SHEDULE = 3,
    WLAN_ACTION_QOS_MAP_CONFIGURE = 4,
};

// DLS_MGMT Action Codes
enum ieee80211_dls_mgmt_actioncode {
    WLAN_ACTION_DLS_REQ = 0,
    WLAN_ACTION_DLS_RESP = 1,
    WLAN_ACTION_DLS_TEARDOWN = 2,
};

// BACK_MGMT Action Codes
enum ieee80211_back_mgmt_actioncode {
    WLAN_ACTION_BACK_ADDBA_REQ = 0,
    WLAN_ACTION_BACK_ADDBA_RESP = 1,
    WLAN_ACTION_BACK_ADDBA_DELBA = 2,
};

// Public_MGMT Action Codes
enum ieee80211_pub_actioncode {
    WLAN_PUB_ACTION_EXT_CHANSW_ANN = 4,
    WLAN_PUB_ACTION_TDLS_DISCOVER_RES = 14,
};

// RADIO_MEASUREMENT_MGMT Action Codes
enum ieee80211_radio_meas_mgmt_actioncode {
    WLAN_ACTION_RADIO_MEAS_REQ = 0,
    WLAN_ACTION_RADIO_MEAS_RPRT = 1,
    WLAN_ACTION_RADIO_MEAS_LINK_MEAS_REQ = 2,
    WLAN_ACTION_RADIO_MEAS_LINK_MEAS_RPRT = 3,
    WLAN_ACTION_RADIO_MEAS_NEIGHBOR_RPRT_REQ = 4,  // 802.11k
    WLAN_ACTION_RADIO_MEAS_NEIGHBOR_RPRT_RESP = 5, // 802.11k
};

// FAST_BSS_TRANSITION_MGMT Action Codes
enum ieee80211_fbsst_mgmt_actioncode {
    WLAN_ACTION_FAST_BSS_T_RESERVED = 0,
    WLAN_ACTION_FAST_BSS_T_REQ = 1,
    WLAN_ACTION_FAST_BSS_T_RESP = 2,
    WLAN_ACTION_FAST_BSS_T_CONFIRM = 3,
    WLAN_ACTION_FAST_BSS_T_ACK = 4,
};

// HT_MGMT Action Codes
enum ieee80211_ht_actioncode { // 802.11n
    WLAN_HT_ACTION_NOTIFY_CHANWIDTH = 0,
    WLAN_HT_ACTION_SMPS = 1,
    WLAN_HT_ACTION_PSMP = 2,
    WLAN_HT_ACTION_PCO_PHASE = 3,
    WLAN_HT_ACTION_CSI = 4,
    WLAN_HT_ACTION_NONCOMPRESSED_BF = 5,
    WLAN_HT_ACTION_COMPRESSED_BF = 6,
    WLAN_HT_ACTION_ASEL_IDX_FEEDBACK = 7,
};

// SA_Query_MGMT Action Codes
enum ieee80211_sa_query_action {
    WLAN_ACTION_SA_QUERY_REQUEST = 0,
    WLAN_ACTION_SA_QUERY_RESPONSE = 1,
};

// Protected_Dual_Of_Action_MGMT Action Codes
enum ieee80211_protect_dual_actioncode {

};

// TDLS_MGMT Action Codes
enum ieee80211_tdls_actioncode { // 802.11z
    WLAN_TDLS_SETUP_REQUEST = 0,
    WLAN_TDLS_SETUP_RESPONSE = 1,
    WLAN_TDLS_SETUP_CONFIRM = 2,
    WLAN_TDLS_TEARDOWN = 3,
    WLAN_TDLS_PEER_TRAFFIC_INDICATION = 4,
    WLAN_TDLS_CHANNEL_SWITCH_REQUEST = 5,
    WLAN_TDLS_CHANNEL_SWITCH_RESPONSE = 6,
    WLAN_TDLS_PEER_PSM_REQUEST = 7,
    WLAN_TDLS_PEER_PSM_RESPONSE = 8,
    WLAN_TDLS_PEER_TRAFFIC_RESPONSE = 9,
    WLAN_TDLS_DISCOVERY_REQUEST = 10,
};

// Mesh_MGMT Action Codes
enum ieee80211_mesh_actioncode { // 802.11s
    WLAN_MESH_ACTION_LINK_METRIC_REPORT,
    WLAN_MESH_ACTION_HWMP_PATH_SELECTION,
    WLAN_MESH_ACTION_GATE_ANNOUNCEMENT,
    WLAN_MESH_ACTION_CONGESTION_CONTROL_NOTIFICATION,
    WLAN_MESH_ACTION_MCCA_SETUP_REQUEST,
    WLAN_MESH_ACTION_MCCA_SETUP_REPLY,
    WLAN_MESH_ACTION_MCCA_ADVERTISEMENT_REQUEST,
    WLAN_MESH_ACTION_MCCA_ADVERTISEMENT,
    WLAN_MESH_ACTION_MCCA_TEARDOWN,
    WLAN_MESH_ACTION_TBTT_ADJUSTMENT_REQUEST,
    WLAN_MESH_ACTION_TBTT_ADJUSTMENT_RESPONSE,
};

// Multihop_MGMT Action Codes
enum ieee80211_multihop_actioncode {

};

// Self_Protected_MGMT Action Codes
enum ieee80211_self_protected_actioncode {
    WLAN_SP_RESERVED = 0,
    WLAN_SP_MESH_PEERING_OPEN = 1,
    WLAN_SP_MESH_PEERING_CONFIRM = 2,
    WLAN_SP_MESH_PEERING_CLOSE = 3,
    WLAN_SP_MGK_INFORM = 4,
    WLAN_SP_MGK_ACK = 5,
};

// DMG_MGMT Action Codes
enum ieee80211_dmg_actioncode {

};

// WMM_MGMT Action Codes
enum ieee80211_wmm_actioncode {

};

// FST_MGMT Action Codes
enum ieee80211_fst_actioncode {

};

// Unprotected_DMG_MGMT Action Codes
enum ieee80211_unproc_dmg_actioncode {

};

// VHT_MGMT Action Codes
enum ieee80211_vht_actioncode { // 802.11ac
    WLAN_VHT_ACTION_COMPRESSED_BF = 0,
    WLAN_VHT_ACTION_GROUPID_MGMT = 1,
    WLAN_VHT_ACTION_OPMODE_NOTIF = 2,
};

// Vendor_Specific_Protected_MGMT Action Codes
enum ieee80211_vendor_spec_proc_actioncode {

};

// Vendor_Specific_MGMT Action Codes
enum ieee80211_vendor_spec_actioncode {

};

// ieee80211, Frame Control Bitmask Parsing Defines And Enumerations
// Frame Type Bit Locations
#define _CTRL_FRAME 2
#define _DATA_FRAME 3

// 802.11 Frame Control Bit Locations
#define _TODS      8
#define _FROMDS    9
#define _MORE     10
#define _RETRY    11
#define _PWRMGT   12
#define _MOREDATA 13
#define _PRIVACY  14
#define _ORDER    15

// Frame Types For Comparison                 LSB     LSB   MSB  TOTAL
enum WIFI_FRAME { //          LSB             Bin  -> Dec | Dec  Dec
    WIFI_MGMT_FRAME = (0              ), // 0 0 0 0  : 0  | 0  = 0
    WIFI_CTRL_FRAME = (         BIT(2)), // 0 1 0 0  : 4  | 0  = 4
    WIFI_DATA_FRAME = (BIT(3)         ), // 1 0 0 0  : 8  | 0  = 8
    WIFI_EXT_FRAME  = (BIT(3) | BIT(2)), // 1 1 0 0  : 12 | 0  = 12 // Wrapper
}; // last 2 bits masked off since type is 2 bits long, really mgmt dec = 0, ctrl dec = 1, data dec = 2, ext dec = 3

// Frame Subtypes For Comparison
enum WIFI_SUBTYPE { //                                                                    MSB     MSB   LSB TOTAL(SUM)
    // Management Frames                      MSB                       LSB               Bin  -> Dec | Dec Dec
    WIFI_ASSOCREQ           = (0                                 | WIFI_MGMT_FRAME), // 0 0 0 0  : 0  | 0 = 0
    WIFI_ASSOCRSP           = (                           BIT(4) | WIFI_MGMT_FRAME), // 0 0 0 1  : 1  | 0 = 16
    WIFI_REASSOCREQ         = (                  BIT(5)          | WIFI_MGMT_FRAME), // 0 0 1 0  : 2  | 0 = 32
    WIFI_REASSOCRSP         = (                  BIT(5) | BIT(4) | WIFI_MGMT_FRAME), // 0 0 1 1  : 3  | 0 = 48
    WIFI_PROBEREQ           = (         BIT(6)                   | WIFI_MGMT_FRAME), // 0 1 0 0  : 4  | 0 = 64
    WIFI_PROBERSP           = (         BIT(6)          | BIT(4) | WIFI_MGMT_FRAME), // 0 1 0 1  : 5  | 0 = 80
    WIFI_BEACON             = (BIT(7)                            | WIFI_MGMT_FRAME), // 1 0 0 0  : 8  | 0 = 96
    WIFI_ATIM               = (BIT(7)                   | BIT(4) | WIFI_MGMT_FRAME), // 1 0 0 1  : 9  | 0 = 112
    WIFI_DISASSOC           = (BIT(7)          | BIT(5)          | WIFI_MGMT_FRAME), // 1 0 1 0  : 10 | 0 = 128
    WIFI_AUTH               = (BIT(7)          | BIT(5) | BIT(4) | WIFI_MGMT_FRAME), // 1 0 1 1  : 11 | 0 = 144
    WIFI_DEAUTH             = (BIT(7) | BIT(6)                   | WIFI_MGMT_FRAME), // 1 1 0 0  : 12 | 0 = 160
    WIFI_ACTION             = (BIT(7) | BIT(6)          | BIT(4) | WIFI_MGMT_FRAME), // 1 1 0 1  : 13 | 0 = 176
    // Control Frames
    WIFI_CTL_EXT            = (         BIT(6) | BIT(5) | BIT(4) | WIFI_CTRL_FRAME), // 0 1 1 1  : 7  | 4 = 116 // Wrapper, 802.11n
    WIFI_BACK_REQ           = (BIT(7)                            | WIFI_CTRL_FRAME), // 1 0 0 0  : 8  | 4 = 132 // BAR
    WIFI_BACK               = (BIT(7)                   | BIT(4) | WIFI_CTRL_FRAME), // 1 0 0 1  : 9  | 4 = 148
    WIFI_PSPOLL             = (BIT(7)          | BIT(5)          | WIFI_CTRL_FRAME), // 1 0 1 0  : 10 | 4 = 164
    WIFI_RTS                = (BIT(7)          | BIT(5) | BIT(4) | WIFI_CTRL_FRAME), // 1 0 1 1  : 11 | 4 = 180
    WIFI_CTS                = (BIT(7) | BIT(6)                   | WIFI_CTRL_FRAME), // 1 1 0 0  : 12 | 4 = 196
    WIFI_ACK                = (BIT(7) | BIT(6)          | BIT(4) | WIFI_CTRL_FRAME), // 1 1 0 1  : 13 | 4 = 212
    WIFI_CFEND              = (BIT(7) | BIT(6) | BIT(5)          | WIFI_CTRL_FRAME), // 1 1 1 0  : 14 | 4 = 228
    WIFI_CFEND_CFACK        = (BIT(7) | BIT(6) | BIT(5) | BIT(4) | WIFI_CTRL_FRAME), // 1 1 1 1  : 15 | 4 = 244
    // Data Frames
    WIFI_DATA               = (0                                 | WIFI_DATA_FRAME), // 0 0 0 0  : 0  | 8 = 8
    WIFI_DATA_CFACK         = (                           BIT(4) | WIFI_DATA_FRAME), // 0 0 0 1  : 1  | 8 = 24
    WIFI_DATA_CFPOLL        = (                  BIT(5)          | WIFI_DATA_FRAME), // 0 0 1 0  : 2  | 8 = 40
    WIFI_DATA_CFACKPOLL     = (                  BIT(5) | BIT(4) | WIFI_DATA_FRAME), // 0 0 1 1  : 3  | 8 = 56
    WIFI_DATA_NULL          = (         BIT(6)                   | WIFI_DATA_FRAME), // 0 1 0 0  : 4  | 8 = 72
    WIFI_CFACK              = (         BIT(6)          | BIT(4) | WIFI_DATA_FRAME), // 0 1 0 1  : 5  | 8 = 88
    WIFI_CFPOLL             = (         BIT(6) | BIT(5)          | WIFI_DATA_FRAME), // 0 1 1 0  : 6  | 8 = 104
    WIFI_CFACKPOLL          = (         BIT(6) | BIT(5) | BIT(4) | WIFI_DATA_FRAME), // 0 1 1 1  : 7  | 8 = 120
    // Quality Of Service Data Frames
    WIFI_QOS_DATA           = (BIT(7)                            | WIFI_DATA_FRAME), // 1 0 0 0  : 8  | 8 = 136
    WIFI_QOS_DATA_CFACK     = (BIT(7)                   | BIT(4) | WIFI_DATA_FRAME), // 1 0 0 1  : 9  | 8 = 152
    WIFI_QOS_DATA_CFPOLL    = (BIT(7)          | BIT(5)          | WIFI_DATA_FRAME), // 1 0 1 0  : 10 | 8 = 168
    WIFI_QOS_DATA_CFACKPOLL = (BIT(7)          | BIT(5) | BIT(4) | WIFI_DATA_FRAME), // 1 0 1 1  : 11 | 8 = 184
    WIFI_QOS_NULL           = (BIT(7) | BIT(6)                   | WIFI_DATA_FRAME), // 1 1 0 0  : 12 | 8 = 200
    WIFI_QOS_CFACK          = (BIT(7) | BIT(6)          | BIT(4) | WIFI_DATA_FRAME), // 1 1 0 1  : 13 | 8 = 216
    WIFI_QOS_CFPOLL         = (BIT(7) | BIT(6) | BIT(5)          | WIFI_DATA_FRAME), // 1 1 1 0  : 14 | 8 = 232
    WIFI_QOS_CFACKPOLL      = (BIT(7) | BIT(6) | BIT(5) | BIT(4) | WIFI_DATA_FRAME), // 1 1 1 1  : 15 | 8 = 248   
};

// Frame Type Octets
#define GetFTypeBit1(p) (CHECKBIT(p, 2)) // first  bit
#define GetFTypeBit2(p) (CHECKBIT(p, 3)) // second bit

// Get Frame Boolean Checks Through Bitshifting
#define GetMGMTF(p) (!GetFTypeBit1(p) && !GetFTypeBit2(p)) // 0x00, management
#define GetCTRLF(p) ( GetFTypeBit1(p) && !GetFTypeBit2(p)) // 0x01, control
#define GetDATAF(p) (!GetFTypeBit1(p) &&  GetFTypeBit2(p)) // 0x10, data
#define GetEXTF(p)  ( GetFTypeBit1(p) &&  GetFTypeBit2(p)) // 0x11, ext

// Expirimentals////////////////////////////////
#define GetCTRL(p) (CHECKBIT(p, _CTRL_FRAME))
#define GetDATA(p) (CHECKBIT(p, _DATA_FRAME))
#define GetMGMT(p) (!GetCTRL(p) && !GetDATA(p))
////////////////////////////////////////////////

#define GetFrameType(p)      ((le16toh(*(us*)(p))) & (BIT(2) | BIT(3)))
#define GetFrameSubType(p)   ((le16toh(*(us*)(p))) & (BIT(2) | BIT(3) | \
                                                      BIT(4) | BIT(5) | \
                                                      BIT(6) | BIT(7)))
#define GetJustFSubType(p)   ((le16toh(*(us*)(p))) & (BIT(4) | BIT(5) | \
                                                      BIT(6) | BIT(7)))
#define GetProtocol(p)       ((le16toh(*(us*)(p))) & (BIT(0) | BIT(1)))
#define GET_IE_RATE(p)       (((u8)p) & (BIT(0) | BIT(1) | BIT(2) | BIT(3) \
                                         BIT(4) | BIT(5) | BIT(6)))
#define GET_IE_RATE_BASIC(p) (((u8)p) & (BIT(7)))

#define GetToDS(p)     (CHECKBIT(p, _TODS))     // To Distribution System
#define GetFromDS(p)   (CHECKBIT(p, _FROMDS))   // From DS
#define GetMoreFlag(p) (CHECKBIT(p, _MORE))     // More
#define GetRetry(p)    (CHECKBIT(p, _RETRY))    // Retry
#define GetPwrMgt(p)   (CHECKBIT(p, _PWRMGT))   // Power Management
#define GetMoreData(p) (CHECKBIT(p, _MOREDATA)) // More Data
#define GetPrivacy(p)  (CHECKBIT(p, _PRIVACY))  // Encryption (WPA/WEP)
#define GetOrder(p)    (CHECKBIT(p, _ORDER))    // Order

// Get Sequence And Fragment
#define FRAG_NUM(x) (le16toh(x)  & 0x000F)
#define SEQ_NUM(x)  ((le16toh(x) & 0xFFF0) >> 4)

// Is Multicast Destination
#define MCAST(da) ((*da) & 0x01)

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// Presentation Length Defines
#define HARDWARE_PRINT_LEN            8 + 8 + 7 + 1
#define ETH_PRINT_LEN                 6 + 6 + 5 + 1
#define IP_PRINT_LEN                  3 + 1 + 3 + 1 + 3 + 1 + 3 + 1
#define IP_PRINT_LEN_6                8 * 4 + 7 + 1                     // 39 + 1 for null
#define IPV4_IN_IPV6_PRINT_LEN        (6 * 4 + 5) + 1 + (4 * 3 + 3) + 1 // 45 + 1 for null
#define OUI_PRINT_LEN                 3 + 3 + 2 + 1
#define IPV6_FLOW_LBL_PRINT_LEN       3 + 3 + 2 + 1
#define WLAN_SA_QUERY_TR_ID_PRINT_LEN 2 + 2 + 1 + 1

// Regular Length Defines
#define IP_ALEN           4
#define OUI_LEN           3
#define IPV6_FLOW_LBL_LEN 3

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// Rx Packet Defines
#define RING_FRAMES 128 // number of frames in ring

// Rx Packet Static Globals
static const long pagesize = sysconf(_SC_PAGESIZE); // pagesize, make sure to check
                                                    // against -1, if using this

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// Typedefs For Radio, ieee80211 Headers
typedef   signed char      s8;
typedef unsigned char      u8;
typedef   signed short     s16;
typedef unsigned short     u16;
typedef   signed /*int*/   s32;
typedef unsigned /*int*/   u32;
typedef   signed long long s64;
typedef unsigned long long u64;

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// Local Data Structure Header Defines
#ifndef WLAN_SA_QUERY_TR_ID_LEN
#define WLAN_SA_QUERY_TR_ID_LEN 2
#endif

// OUI's
static u8 oui_rfc1042[OUI_LEN]   = {0x00, 0x00, 0x00}; // ethernet encapsulation(rfc1042)
static u8 oui_cisco[OUI_LEN]     = {0x00, 0x0B, 0x85}; // Cisco Systems, Inc.
static u8 oui_cisco2[OUI_LEN]    = {0x00, 0x40, 0x96}; // Cisco Systems, Inc.
static u8 oui_apple[OUI_LEN]     = {0x00, 0x17, 0xF2}; // Apple
static u8 oui_microsoft[OUI_LEN] = {0x00, 0x50, 0xF2}; // Microsoft Corp.
static u8 oui_broadcom[OUI_LEN]  = {0x00, 0x10, 0x18}; // Broadcom Corp.
static u8 oui_samsung[OUI_LEN]   = {0x00, 0x16, 0x32}; // Samsung Electronics CO., LTD.
static u8 oui_atheros[OUI_LEN]   = {0x00, 0x03, 0x7F}; // Atheros Communications, Inc.
static u8 oui_aerohive[OUI_LEN]  = {0x00, 0x19, 0x77}; // Aerohive Networks, Inc.
static u8 oui_ieee80211[OUI_LEN] = {0x00, 0x0F, 0xAC}; // IEEE 802.11, Used Mainly For RSN IE

// Some OUI's ether_type
static u16 CISCO_OTAP_ETHER_TYPE    = 0xCCCD; // OTAP Cisco ether_type, with cisco[] oui
static u16 CISCO_AIRONET_ETHER_TYPE = 0x0000; // Aironet Cisco ether_type with cisco2[] oui

// Radio Frequency Header, Regular
typedef struct {
    u8     it_version,    // should be zero
           it_pad;
    __le16 it_len;
    __le32 it_present;
}__packed ie80211_rtaphdr;

// Radiotap Header, For RX
typedef struct {
    u8     it_version,    // should be zero
           it_pad;
    __le16 it_len;
    __le32 it_present;    // bitmask presents
    u64    rt_tsft;       // mactime(micro secs)
    u8     rt_flags,
           rt_rate;       // RX(500 Kbps)
    u16    rt_chan,       // MHz/GHz
           rt_chan_flags;
    s8     rt_antsignal,  // RF dBm
           rt_antnoise;   // RF dBm
    u8     rt_antenna,    // antenna index
           rt_pad[3];     // pad for 4 byte boundary
}__packed ie80211_rtaphdr_rx;

// Radiotap Header, For TX
typedef struct {
    u8     it_version,    // should be zero
           it_pad;        // pad for len
    __le16 it_len;
    __le32 it_present;
    u8     rt_rate,       // TX(500 Kbps)
           rt_pad;        // pad for chan
    u16    rt_chan,       // MHz/GHz
           rt_chan_flags;
    s8     rt_antsignal;  // RF dBm
    u8     rt_antenna;    // antenna index
}__packed ie80211_rtaphdr_tx;

// 802.11 Frame Check Sequence
typedef struct {
    __le32 fcs;
} ieee80211_fcs_hdr;

// 802.11 Frame Header, 3 Addresses
typedef struct {
    __le16 frame_control,
           duration_id;
    u8     addr1[ETH_ALEN],
           addr2[ETH_ALEN],
           addr3[ETH_ALEN];
    __le16 seq_ctrl;
}__packed __aligned(2) ieee80211_hdr3; // alligned 2 byte boundary

//  802.11 Frame Header, 4 Addresses
typedef struct {
    __le16 frame_control,
           duration_id;
    u8     addr1[ETH_ALEN],
           addr2[ETH_ALEN],
           addr3[ETH_ALEN];
    __le16 seq_ctrl;
    u8     addr4[ETH_ALEN];
}__packed __aligned(2) ieee80211_hdr4;

// 802.11 Frame Header, Control Frames
typedef struct {
    __le16 frame_control,
           duration;
    u8     ra[ETH_ALEN],
           ta[ETH_ALEN];
}__packed __aligned(2) ieee80211_rts_hdr,      // RTS, (NAV)
                       ieee80211_cfendack_hdr; // CF-End + CF-Ack, (PCF)

typedef struct {
    __le16 frame_control,
           duration;
    u8     ra[ETH_ALEN];
}__packed __aligned(2) ieee80211_cts_hdr,   // CTS, (NAV)
                       ieee80211_cfend_hdr, // CF-End, (PCF)
                       ieee80211_ack_hdr;   // Ack

typedef struct {
    __le16 frame_control,
           aid;
    u8     bssid[ETH_ALEN],
           ta[ETH_ALEN];
}__packed __aligned(2) ieee80211_pspoll_hdr; // PS-Poll

typedef struct {
    __le16 frame_control,
           duration;
    u8     ra[ETH_ALEN],
           ta[ETH_ALEN];
    __le16 bar_ctrl,
           start_seq_ctrl;
}__packed __aligned(2) ieee80211_backreq_hdr; // BAR(BACK-Req)

typedef struct {
    __le16 frame_control,
           duration;
    u8     ra[ETH_ALEN],
           ta[ETH_ALEN];
    __le16 bar_ctrl,
           start_seq_ctrl;
    __le64 bitmap;
}__packed __aligned(2) ieee80211_back_hdr; // BACK

typedef struct {
    __le16 frame_control,
           duration;
    u8     ra[ETH_ALEN];
    __le16 carried_frame_ctrl,
           ht_ctrl;
}__packed __aligned(2) ieee80211_ctrlext_hdr; // Control Wrapper EXT

// 802.11 Frame Header, Management Action Frame IEs
typedef struct {
    u8 mode,
       new_operating_class,
       new_ch_num,
       count;
}__packed ieee80211_ext_chansw_ie;

typedef struct {
    u8 token,
       mode,
       type,
       request[0];
}__packed ieee80211_msrment_ie;

typedef struct {
    u8 tx_power,
       link_margin;
}__packed ieee80211_tpc_report_ie;

/* Information Elements Following ieee80211 MGMT Frames */
// SSID IE
typedef struct {
    u8 id,
       len,
       ssid[0];
}__packed ieee80211_ie_ssid;

// Rates IE
typedef struct {
    u8 id,
       len,
       rates[0];
}__packed ieee80211_ie_rates;

// Request IE
typedef struct {
    u8 id,
       len,
       request[0];
}__packed ieee80211_ie_request;

// Challenge Text IE(Shared Key Authentication)
typedef struct {
    u8 id,
       len,
       challenge_text[0];
}__packed ieee80211_ie_challenge;

// Power Constraint IE
typedef struct {
    u8 id,
       len,
       pwr_constraint;
}__packed ieee80211_ie_pwr_constraint;

// ERP IE(PHY Level Flags)
typedef struct {
    u8 id,
       len,
       erp_info;
}__packed ieee80211_ie_erp_info;

// Vendor Specific IE
typedef struct {
    u8     id,
           len;
    __le32 oui;
    u8     data[0];
}__packed ieee80211_ie_vendor;

// Robust Security Network(WPA) IE
typedef struct {
    u8     id,
           len,
           version;
    __le32 group_cipher; // for multicast/broadcast
    __le16 pairwise_count; // unicast cipher count
    __le32 pairwise_cipher[0]; // unicast cipher ID list
    __le16 auth_count; // authentication types supported count
    __le32 auth_list[0]; // authentication types list
    __le16 rsn_capab; // security capabilities, rsn only
    __le16 pmkid_count; // PMKIDs count, association frames only
    u8     pmkid_list[0]; // PMKIDs list, 16-byte SHA1 type
}__packed ieee80211_ie_rsn;

// Channels IE Channel Band Tuple
typedef struct ieee80211_ie_channels_channel_band {
    u8 first_channel,
       nr_channels;
}__packed ieee80211_ie_channels_channel_band;

typedef struct ieee80211_ie_channels {
    u8 id,
       len;
    ieee80211_ie_channels_channel_band channels[0];
}__packed ieee80211_ie_channels;

// Direct Spectrum(Channel Number) IE
typedef struct {
    u8 id,
       len,
       cur_chan;
}__packed ieee80211_ie_ds_param;

// Country IE Regulatory Extension Triplet
typedef struct {
    u8 reg_ext_id,
       reg_class_id,
       coverage_class;
}__packed ieee80211_ie_country_ext_triplet;
 
// Country IE Regulatory Band Triplet
typedef struct {
    u8 first_channel,
       nr_channels,
       max_txpwr;
}__packed ieee80211_ie_country_band_triplet;

// Country IE Regulatory Triplet
/* Band triplet if the first byte < 200, extension triplet otherwise */
typedef union {
    u8 first; // differentiator between band and ext triplets
    ieee80211_ie_country_band_triplet band;
    ieee80211_ie_country_ext_triplet  ext;
} ieee80211_ie_country_triplet;

// Country IE
#define IE_COUNTRY_CODE_LEN 2
typedef struct {
    u8 id,
       len,
       name[IE_COUNTRY_CODE_LEN], // ISO Alpha2 country code
       in_out;  // 'I' for indoor, 'O' for outdoor
    ieee80211_ie_country_triplet triplet[0]; // regulatory triplet list
}__packed ieee80211_ie_country;

// Power Capabilities IE
typedef struct {
    u8 id,
       len,
       min_txpwr,
       max_txpwr;
}__packed ieee80211_ie_power_capab;

// Traffic Indication Map
typedef struct {
    u8 id,
       len,
       DTIM_count,
       DTIM_period,
       bitmap_ctrl,
       partial_virtual_bitmap;
}__packed ieee80211_ie_tim;

typedef struct {
    u8 id,
       len,
       tx_power,
       link_margin;
}__packed ieee80211_ie_tpc;

typedef struct {
    u8     id,
           len;
    __le16 capab_info;
    u8     a_mpdu_param;
    u8     mcs_set[16]; // supported modulation and codeing scheme
    __le16 extended_capab;
    __le32 trans_beamform_capab;
    u8     antenna_capab; // antenna selection
}__packed ieee80211_ie_ht_capab;

// Generic IE For Our Union Below
typedef struct {
    u8 id,
       len;
    union {
        u8 ssid[0],
           rates[0],
           request[0],
           challenge_text[0],
           power_constraint,
           erp_info;
        ieee80211_ie_channels_channel_band channels[0];
    };
}__packed ieee80211_ie_generic;

// Used In Place Of variable[0] in MGMT Sub-Frames
typedef union {
    // Generic Information Element
    ieee80211_ie_generic ie_gen;

    // DS Parameters
    ieee80211_ie_ds_param ds_param;

    // TIM
    ieee80211_ie_tim tim;

    // TPC Report
    ieee80211_ie_tpc tpc_report;

    // Country Info
    ieee80211_ie_country country;

    // Power Capabilities
    ieee80211_ie_power_capab power_capab;
 
    // Security Info
    ieee80211_ie_rsn rsn;

    // HT Capabilities
    ieee80211_ie_ht_capab ht_capab;

    // Vendor Specific
    ieee80211_ie_vendor vendor;

    // Add More
} ieee80211_ie;

// 802.11 Frame Header, Management Frame
/* using own ieee80211_ie union as c-hack flexible array instead of variable[0] */
typedef struct {
    __le16 frame_control,
           duration;
    u8     da[ETH_ALEN],
           sa[ETH_ALEN],
           bssid[ETH_ALEN];
    __le16 seq_ctrl;
    
    union {
        struct {
            __le16 auth_alg,
                   auth_transaction,
                   status_code;
            /* challenge text possible */
            ieee80211_ie ie[0];
        }__packed auth;
        
        struct {
            __le16 reason_code;
        }__packed deauth;
        
        struct {
            __le16 capab_info,
                   listen_interval;
            /* SSID and supported rates */
            ieee80211_ie ie[0];
        }__packed assoc_req;
        
        struct {
            __le16 capab_info,
                   status_code,
                   aid;
            /* supported rates */
            ieee80211_ie ie[0];
        }__packed assoc_resp, reassoc_resp;
        
        struct {
            __le16 capab_info,
                   listen_interval;
            u8     current_ap[ETH_ALEN];
            /* SSID and supported rates */
            ieee80211_ie ie[0];
        }__packed reassoc_req;

        struct {
            __le16 reason_code;
        }__packed disassoc;

        struct {
            __le64 timestamp;
            __le16 beacon_int,
                   capab_info;
            /* SSID, supported rates, FH params, DS params, CF params, IBSS params, TIM */
            ieee80211_ie ie[0];
        }__packed beacon;

        struct {
            /* SSID, supported rates */
            ieee80211_ie ie[0];
        }__packed probe_req;
        
        struct {
            __le64 timestamp;
            __le16 beacon_int,
                   capab_info;
            /* SSID, supported rates, FH params, DS params, CF params, IBSS params */
            ieee80211_ie ie[0];
        }__packed probe_resp;
        
        struct {
            u8 category; // differentiator for action
            
            union {
                struct {
                    u8 action_code,
                       dialog_token,
                       status_code,
                       variable[0];
                }__packed wme_action;

                struct {
                    u8 action_code,
                       variable[0];
                }__packed chan_switch;
                
                struct {
                    u8 action_code;
                    ieee80211_ext_chansw_ie data;
                    u8 variable[0];
                }__packed ext_chan_switch;

                struct {
                    u8 action_code,
                       dialog_token,
                       element_id,
                       length;
                    ieee80211_msrment_ie msr_elem;
                }__packed measurement;
                
                struct {
                    u8     action_code,
                           dialog_token;
                    __le16 capab,
                           timeout,
                           start_seq_num;
                }__packed addba_req;
                
                struct {
                    u8     action_code,
                           dialog_token;
                    __le16 status,
                           capab,
                           timeout;
                }__packed addba_resp;
                
                struct {
                    u8     action_code;
                    __le16 params,
                           reason_code;
                }__packed delba;
                
                struct {
                    u8 action_code,
                       variable[0];
                }__packed self_prot;
                
                struct {
                    u8 action_code,
                       variable[0];
                }__packed mesh_action;

                struct {
                    u8 action_code,
                       trans_id[WLAN_SA_QUERY_TR_ID_LEN];
                }__packed sa_query;
                
                struct {
                    u8 action_code,
                       smps_control;
                }__packed ht_smps;
                
                struct {
                    u8 action_code,
                       chanwidth;
                }__packed ht_notify_cw;
                
                struct {
                    u8     action_code,
                           dialog_token;
                    __le16 capability;
                    u8     variable[0];
                }__packed tdls_discover_resp;

                struct {
                    u8 action_code,
                       operating_mode;
                }__packed vht_opmode_notif;
                
                struct {
                    u8 action_code,
                       dialog_token,
                       tpc_elem_id,
                       tpc_elem_length;
                    ieee80211_tpc_report_ie tpc;
                }__packed tpc_report;
            } u;
        }__packed action;
    } u;
}__packed __aligned(2) ieee80211_mgmt_hdr;

// 802.11 Frame Header, Quality Of Service Frames
typedef struct {
    __le16 frame_control,
           duration_id;
    u8     addr1[ETH_ALEN],
           addr2[ETH_ALEN],
           addr3[ETH_ALEN];
    __le16 seq_ctrl,
           qos_ctrl;
}__packed __aligned(2) ieee80211_qos_hdr3; // 3 addrs

typedef struct {
    __le16 frame_ctl,
           duration_id;
    u8     addr1[ETH_ALEN],
           addr2[ETH_ALEN],
           addr3[ETH_ALEN];
    __le16 seq_ctrl;
    u8     addr4[ETH_ALEN];
    __le16 qos_ctrl;
}__packed __aligned(2) ieee80211_qos_hdr4; // 4 addrs

// 802.11 Frame Header, QOS HT Frames, Order Bit=1
typedef struct {
    __le16 frame_control,
           duration_id;
    u8     addr1[ETH_ALEN],
           addr2[ETH_ALEN],
           addr3[ETH_ALEN];
    __le16 seq_ctrl,
           qos_ctrl;
    __le32 ht_ctrl;
}__packed __aligned(2) ieee80211_ht_hdr3; // 3 addrs

typedef struct {
    __le16 frame_ctl,
           duration_id;
    u8     addr1[ETH_ALEN],
           addr2[ETH_ALEN],
           addr3[ETH_ALEN];
    __le16 seq_ctrl;
    u8     addr4[ETH_ALEN];
    __le16 qos_ctrl;
    __le32 ht_ctrl;
}__packed __aligned(2) ieee80211_ht_hdr4; // 4 addrs

// Union Our ieee80211 Frame Headers
typedef union {                    
    ieee80211_hdr3         ieee80211_3;        // generic 3 addrs
    ieee80211_hdr4         ieee80211_4;        // generic 4 addrs
    ieee80211_rts_hdr      ieee80211_rts;      // RTS Control
    ieee80211_cts_hdr      ieee80211_cts;      // CTS Control
    ieee80211_ack_hdr      ieee80211_ack;      // ACK Control
    ieee80211_cfend_hdr    ieee80211_cfend;    // CF-End Control
    ieee80211_cfendack_hdr ieee80211_cfendack; // CF-End + CF_Ack Control
    ieee80211_back_hdr     ieee80211_back;     // BACK Control
    ieee80211_backreq_hdr  ieee80211_backreq;  // BAR(BACK-Req) Control
    ieee80211_ctrlext_hdr  ieee80211_ctrlext;  // Ctrl-Ext(Control Extension) Wrapper
    ieee80211_pspoll_hdr   ieee80211_pspoll;   // PS-Poll Control
    ieee80211_mgmt_hdr     ieee80211_mgmt;     // Management
    ieee80211_qos_hdr3     ieee80211_qos_3;    // Quality Of Service Data 3 addrs
    ieee80211_qos_hdr4     ieee80211_qos_4;    // Quality Of Service Data 4 addrs
    ieee80211_ht_hdr3      ieee80211_ht_3;     // QOS HT 3 addrs
    ieee80211_ht_hdr4      ieee80211_ht_4;     // QOS HT 4 addrs
    const unsigned char    ieee80211_craw;     // const raw header
          unsigned char    ieee80211_raw;      // raw raw header, carefual not to mutate data
} u_ieee80211_hdrs;

// Logical Link Control(upper data-link) Frame Header, 802.2
typedef struct {
    // LLC Header Start
    u8 dsap,       // destination service access point
       ssap,       // source      service access point
       ctrl1;      // LLC control field frame type, 1st octet (U-format)
     //ctrl2;      //                             , 2nd octet (I/S-formats)
}__packed llc_hdr;

// SubNetwork Access Protocol(upper data-link LLC extension) Frame Header
#define IEEE80211_SNAP_ETH_802_3_ON  true  // for printing the headers
#define IEEE80211_SNAP_ETH_802_3_OFF false

typedef struct {
    // SNAP Extension Header Start
    u8     oui[OUI_LEN]; // organizationally unique identifier, 3 octets
    __be16 ether_type;   // for backwards compatability with ethernet II frame
}__packed snap_hdr;

// LLC + SNAP Frame Header
typedef struct {
    // LLC Header Start
    u8     dsap,         // destination service access point
           ssap,         // source      service access point
           ctrl1;        // LLC control field frame type, 1st octet
         //ctrl2;        //                             , 2nd octet
    // SNAP Extension Header Start
    u8     oui[OUI_LEN]; // organizationally unique identifier
    __be16 ether_type;   // for backwards compatability with ethernet II frame
}__packed llc_snap_hdr; // combined LLC + SNAP Extension

typedef struct {
    u16 protoID;
    u8  version,
        msg_type,
        flags;
    u8  rootID[8];   // 16 bit priority, 48 bit mac
    u32 root_pathCost;
    u8  bridgeID[8]; // 16 but priority, 48 bit mac
    u16 portID,
        msg_age,
        max_time,
        hello_time,
        fwrd_delay;
} __packed stphdr;

// Declare Our Own ARP Header For Non-Commented Out Addresses
typedef struct {
    __be16 ar_hrd,
           ar_pro;
    u8     ar_hln,
           ar_pln;
    __be16 ar_op;
    u8     ar_sha[ETH_ALEN],
           ar_sip[IP_ALEN],
           ar_tha[ETH_ALEN],
           ar_tip[IP_ALEN];
} arphdr2;
 
// Declare Our Own SCTP Header
typedef struct {
    __be16 source,
           dest;
    __be32 vtag,
           checksum;
} sctphdr2;
 
// Declare Our Own SCTP Chunk Header
typedef struct {
    u8     type,
           flags;
    __be16 length;
} sctp_chunkhdr2;

// Declare Out Own IPv6 Header
typedef struct {
#if defined(__LITTLE_ENDIAN_BITFIELD) // bitfields
    u8 priority:4,                    // 4 bits(nibble)
       version :4;
#elif defined(__BIG_ENDIAN_BITFIELD)
    u8 version :4,
       priority:4;
#else
#error "fix <asm/byteorder.h>"
#endif

    u8       flow_lbl[IPV6_FLOW_LBL_LEN];
    __be16   payload_len;
    u8       nexthdr,
             hop_limit;
    in6_addr saddr,
             daddr;
} ipv6hdr;

// Extensible Authentication Protocol, PAE 802.1X
typedef struct {
    u8  code,
        eapid;
    u16 length; ///////////////////////////////////////////////////////////////////////////////////fix eap
}__packed EAP_hdr;

// Extensible Authentication Protocol Over LAN, EAPoL
typedef struct {
    u8  version,
        type;
    u16 length;
}__packed eapolhdr;

enum eap_type {
    EAP_PACKET = 0,
    EAPOL_START,
    EAPOL_LOGOFF,
    EAPOL_KEY,
    EAPOL_ENCAP_ASF_ALERT
};

// Block Descending For Packet V3, Can Include <net/psock_tpacket.c>
typedef struct { // walking the block, V3
    uint32_t       version,
                   offset_to_priv;
    tpacket_hdr_v1 h1;
} block_desc;

// Ring Vector, Map, Request For Packet V3
typedef struct {
	iovec        *rd;
	uint8_t      *map;
	tpacket_req3  req;
} ringVec;

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// Mix MAC Addresses                    /* Hash Functions, Bob Jenkins */
#define mix(a, b, c)                    \
    do {                                \
        a -= b; a -= c; a ^= (c >> 13); \
        b -= c; b -= a; b ^= (a <<  8); \
        c -= a; c -= b; c ^= (b >> 13); \
        a -= b; a -= c; a ^= (c >> 12); \
        b -= c; b -= a; b ^= (a << 16); \
        c -= a; c -= b; c ^= (b >>  5); \
        a -= b; a -= c; a ^= (c >>  3); \
        b -= c; b -= a; b ^= (a << 10); \
        c -= a; c -= b; c ^= (b >> 15); \
    }while(0) // const condition

static uint32_t mac_hash(const uint32_t hash_key, const uint8_t addr[ETH_ALEN]) { // hash mac
    uint32_t a = 0x9e3779b9, b = 0x9e3779b9, c = hash_key;

    b += addr[5] << 8;
    b += addr[4];
    a += addr[3] << 24;
    a += addr[2] << 16;
    a += addr[1] << 8;
    a += addr[0];
 
    mix(a, b, c);
    return c;
}

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// BPF Filter Defines
#define PROMISCFILTER       0 // filter All
#define TCPFILTER           1 // filter TCP
#define UDPFILTER           2 // filter UDP
#define SCTPFILTER          3 // filter SCTP
#define ICMPFILTER          4 // filter ICMP
#define IGMPFILTER          5 // filter IGMP
#define ARPFILTER           6 // filter ARP
#define MACFILTER           7 // filter MAC
#define IPFILTER            8 // filter IP
#define BCAST_UNCAST_FILTER 9 // filter Broadcast and Unicast

// Statics For BPF
static const std::size_t ARPSIZE = sizeof(ethhdr) + sizeof(arphdr2);
static const std::size_t IPSIZE  = sizeof(ethhdr) + sizeof(iphdr);
static in_port_t         PORT    = 0;

// Conversion Define, MAC Filtering For BPF
#define ETHER_FIRST_INT(e)	((e)[0] << 24 | (e)[1] << 16 | (e)[2] << 8 | (e)[3])
#define ETHER_LAST_SHORT(e)	((e)[4] <<  8 | (e)[5])

// Sniffer Class Definitions Start Here
//>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
int Sniffer::attach_filter(c_char_ptrc ifc, cuchar_cptr smac, int sfd, c_uint fType) {
    // Declarations
    sock_fprog  fprog;
    sock_filter *s_filter = NULL;
    unsigned char tempmac[ETH_PRINT_LEN];
    
    // Zero Out
    std::memset(&fprog,  0, sizeof(fprog));
    std::memset(tempmac, 0, ETH_PRINT_LEN);

    if(fType == PROMISCFILTER) {
        // Filter All
        sock_filter promiscfilter[] = {
            BPF_STMT(BPF_RET, (u_int)-1) // return all frames
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(promiscfilter)))) {
            std::perror("malloc");
            return -1;
        }

        // Copy In
        std::memcpy(s_filter, &promiscfilter, sizeof(promiscfilter));

        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(promiscfilter)/sizeof(sock_filter);
    }
    else if(fType == MACFILTER) {
        // Filter MAC Broadcast And Unicast Packets
        cuchar_cptr mac = (cuchar_cptr)"FF:FF:FF:FF:FF:FF";
        sock_filter bcast_unicastfilter[] = {                                
		    BPF_STMT(BPF_LD  + BPF_W   + BPF_ABS, 0),
		    BPF_JUMP(BPF_JMP + BPF_JEQ + BPF_K,   (u_int)ETHER_FIRST_INT((cuchar_cptr)ether_aton((char*)mac)),  0, 3),
		    BPF_STMT(BPF_LD  + BPF_H   + BPF_ABS, 4),
		    BPF_JUMP(BPF_JMP + BPF_JEQ + BPF_K,   (u_int)ETHER_LAST_SHORT((cuchar_cptr)ether_aton((char*)mac)), 0, 1),
	    	BPF_STMT(BPF_RET + BPF_K,    (u_int)-1),
		    BPF_STMT(BPF_RET + BPF_K,    (u_int) 0),
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(bcast_unicastfilter)))) {
            std::perror("malloc");
            return -1;
        }
    
        // Copy In
        std::memcpy(s_filter, &bcast_unicastfilter, sizeof(bcast_unicastfilter));

        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(bcast_unicastfilter)/sizeof(sock_filter);
    }
    else if(fType == BCAST_UNCAST_FILTER) {
        // Filter MAC Broadcast And Unicast Packets
        sock_filter bcast_unicastfilter[] = {                                
            BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 6),                // A <- P[2:4]
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   0xffffffff, 0, 2), // if A != broadcast GOTO LABEL
            BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 0),                // A <- P[0:2]
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   0x0000ffff, 2, 0), // if A == unicast   GOTO ACCEPT
            // LABEL
            BPF_STMT(BPF_LD  + BPF_B    + BPF_ABS, 0),                // A <- P[0:1]
            BPF_JUMP(BPF_JMP + BPF_JSET + BPF_K,   0x01,       0, 1), // if !(A & 1)       GOTO REJECT
            // ACCEPT
            BPF_STMT(BPF_RET, ETH_FRAME_LEN),                         // return size ethernet frame
            // REJECT
            BPF_STMT(BPF_RET, 0),                                     // return null
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(bcast_unicastfilter)))) {
            std::perror("malloc");
            return -1;
        }
    
        // Copy In
        std::memcpy(s_filter, &bcast_unicastfilter, sizeof(bcast_unicastfilter));

        // Adjust(shift) For Fake MAC Address
        s_filter[1].k = (smac[2] & 0xff) << 24 |
                        (smac[3] & 0xff) << 16 |
                        (smac[4] & 0xff) << 8  |
                        (smac[5] & 0xff);
        s_filter[3].k = (smac[0] & 0xff) << 8  |
                        (smac[1] & 0xff);

        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(bcast_unicastfilter)/sizeof(sock_filter);
    }
    else if(fType == ARPFILTER) {
        // Filter ARP Frames
        sock_filter arpfilter[] = {
            // Instructions
            BPF_STMT(BPF_LD  + BPF_H   + BPF_ABS, 12),              // fixed offset = ethernet hardware address
            BPF_JUMP(BPF_JMP + BPF_JEQ + BPF_K,   ETH_P_ARP, 0, 1), // eth hardware addr != ARP, skip next instruc
            // Access
            BPF_STMT(BPF_RET + BPF_K,    ARPSIZE),                  // return ARP frame
            // Drop
            BPF_STMT(BPF_RET + BPF_K,    0),                        // return null
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(arpfilter)))) {
            std::perror("malloc");
            return -1;
        }

        // Copy In
        std::memcpy(s_filter, &arpfilter, sizeof(arpfilter));
 
        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(arpfilter)/sizeof(sock_filter);
    }
    else if(fType == IPFILTER) {
        // Filter IP Packets
        sock_filter ipfilter[] = {
           // Instructions
            BPF_STMT(BPF_LD  + BPF_H   + BPF_ABS, 12),             // fixed offset = ethernet hardware address
            BPF_JUMP(BPF_JMP + BPF_JEQ + BPF_K,   ETH_P_IP, 0, 1), // eth hardware addr != IP, skip next instruc
            // Accept
            BPF_STMT(BPF_RET + BPF_K,    IPSIZE),                  // return IP packet
            // Drop
            BPF_STMT(BPF_RET + BPF_K,    0),                       // return null
        };
        
        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(ipfilter)))) {
            std::perror("malloc");
            return -1;
        }

        // Copy In
        std::memcpy(s_filter, &ipfilter, sizeof(ipfilter));
 
        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(ipfilter)/sizeof(sock_filter);
    }
    /*else if(fType == TCPFILTER) {
        // Filter TCP Packets
        sock_filter tcpfilter[] = {                                     // ***Detailed Instructions For Learning***
            // Instructions
	        BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 12),                 // fixed offset = ethernet hardware addr  (half word load)
	        BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   ETH_P_IP,    0, 10), // eth hardware addr != IP, skip next 10 instruc
            BPF_STMT(BPF_LD  + BPF_B    + BPF_ABS, 23),                 // offset = IP protocol                   (byte load)
	        BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   IPPROTO_TCP, 0, 8),  // protocol != TCP, skip next 8 instruc
	        BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 20),                 // offset = flags, fragment offset        (half word load)
	        BPF_JUMP(BPF_JMP + BPF_JSET + BPF_K,   0x1fff,      6, 0),  // ((R,DF,MF = 0, fragOff = 8191(MAX)) & Current Flags, FOff), 
                                                                        // true, skip next 6 instruc
	        BPF_STMT(BPF_LDX + BPF_B    + BPF_MSH, 14),                 // offset = IP version + IP header length (byte index load)
                                                                        // load IP header len(14) into register (MSH, IP hdr len hack)
            BPF_STMT(BPF_LD  + BPF_H    + BPF_IND, 14),                 // variable offset = TCP source port      (half word load)
                                                                        // 14 + len in index register
            // Filter By Port
	        BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   PORT,        2, 0),  // source port == 80, skip next 2 instruc
	        BPF_STMT(BPF_LD  + BPF_H    + BPF_IND, 16),                 // variable offset = dest port            (half word load)
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   PORT,        0, 1),  // dest port != 80, skip next instruc
            // Accept
            BPF_STMT(BPF_RET + BPF_K,     (u_int)-1),                   // return TCP packet                      (constant)
            // Drop
	        BPF_STMT(BPF_RET + BPF_K,     0),                           // return null                            (constant)
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(tcpfilter)))) {
            std::perror("malloc");
            return -1;
        }
    
        // Copy In
        std::memcpy(s_filter, &tcpfilter, sizeof(tcpfilter));

        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(tcpfilter)/sizeof(sock_filter);
    }*/
    else if(fType == UDPFILTER) {
        // Filter UDP - All Port Packets
        sock_filter udpfilter[] = {
            // Instructions
            BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 12),                 // fixed offset = ethernet hardware address
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   ETH_P_IP,    0, 10), // eth hardware addr != IP, skip next 10 instruc
            BPF_STMT(BPF_LD  + BPF_B    + BPF_ABS, 23),                 // offset = IP protocol
	        BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   IPPROTO_UDP, 0, 8),  // protocol != UDP, skip next 8 instruc
	        BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 20),                 // offset = flags, fragment offset   
            BPF_JUMP(BPF_JMP + BPF_JSET + BPF_K,   0x1fff,      6, 0),  // ((R,DF,MF = 0, fragOff = 8191(MAX)) & Current Flags, Foff),
                                                                        // true, skip next 6 instruc
            BPF_STMT(BPF_LDX + BPF_B    + BPF_MSH, 14),                 // offset = IP version + IP header length
                                                                        // load IP header len(14) into register
            BPF_STMT(BPF_LD  + BPF_H    + BPF_IND, 14),                 // variable offset = UDP source port
            // Filter By Port
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   PORT,        2, 0),  // source port == 80, skip next 2 instruc
            BPF_STMT(BPF_LD  + BPF_H    + BPF_IND, 16),                 // variable offset = dest port
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   PORT,        0, 1),  // dest port != 80, skip next instruc
            // Accept
            BPF_STMT(BPF_RET + BPF_K,     (u_int)-1),                   // return UDP packet
            // Drop
	        BPF_STMT(BPF_RET + BPF_K,     0),                           // return null
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(udpfilter)))) {
            std::perror("malloc");
            return -1;
        }

        // Copy In
        std::memcpy(s_filter, &udpfilter, sizeof(udpfilter));
 
        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(udpfilter)/sizeof(sock_filter);
    }
    else if(fType == SCTPFILTER) {
        // Filter SCTP - All Port Packets
        sock_filter sctpfilter[] = {
            // Instructions
            BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 12),                  // fixed offset = ethernet hardware address
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   ETH_P_IP,     0, 10), // eth hardware addr != IP, skip next 10 instruc
            BPF_STMT(BPF_LD  + BPF_B    + BPF_ABS, 23),                  // offset = IP protocol
	        BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   IPPROTO_SCTP, 0, 8),  // protocol != SCTP, skip next 8 instruc
	        BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 20),                  // offset = flags, fragment offset   
            BPF_JUMP(BPF_JMP + BPF_JSET + BPF_K,   0x1fff,       6, 0),  // ((R,DF,MF = 0, fragOff = 8191(MAX)) & Current Flags, FOff),
                                                                         // true, skip next 6 instruc
            BPF_STMT(BPF_LDX + BPF_B    + BPF_MSH, 14),                  // offset = IP version + IP header length
                                                                         // load IP header len(14) into register
            BPF_STMT(BPF_LD  + BPF_H    + BPF_IND, 14),                  // variable offset = SCTP source port
            // Filter By Port
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   PORT,         2, 0),  // source port == 80, skip next 2 instruc
            BPF_STMT(BPF_LD  + BPF_H    + BPF_IND, 16),                  // variable offset = dest port
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   PORT,         0, 1),  // dest port != 80, skip next instruc
            // Accept
            BPF_STMT(BPF_RET + BPF_K,     (u_int)-1),                    // return UDP packet
            // Drop
	        BPF_STMT(BPF_RET + BPF_K,     0),                            // return null
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(sctpfilter)))) {
            std::perror("malloc");
            return -1;
        }

        // Copy In
        std::memcpy(s_filter, &sctpfilter, sizeof(sctpfilter));
 
        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(sctpfilter)/sizeof(sock_filter);
    }
    else if(fType == ICMPFILTER) {
        // Filter ICMP Packets
        sock_filter icmpfilter[] = {
            // Instructions
            BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 12),                 // fixed offset = ethernet hardware address
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   ETH_P_IP,     0, 7), // eth hardware addr != IP, skip next 7 instruc
            BPF_STMT(BPF_LD  + BPF_B    + BPF_ABS, 23),                 // offset = IP protocol
	        BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   IPPROTO_ICMP, 0, 5), // protocol != ICMP, skip next 5 instruc
	        BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 20),                 // offset = flags, fragment offset   
            BPF_JUMP(BPF_JMP + BPF_JSET + BPF_K,   0x1fff,       3, 0), // ((R,DF,MF = 0, fragOff = 8191(MAX)) & Current Flags, FOff),
                                                                        // true, skip next 3 instruc
            BPF_STMT(BPF_LDX + BPF_B    + BPF_MSH, 14),                 // offset = IP version + IP header length
                                                                        // load IP header len(14) into register
            BPF_STMT(BPF_LD  + BPF_H    + BPF_IND, 14),                 // variable offset = ICMP type
            // Accept
            BPF_STMT(BPF_RET + BPF_K,     (u_int)-1),                   // return ICMP packet
            // Drop
	        BPF_STMT(BPF_RET + BPF_K,     0),                           // return null
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(icmpfilter)))) {
            std::perror("malloc");
            return -1;
        }

        // Copy In
        std::memcpy(s_filter, &icmpfilter, sizeof(icmpfilter));
 
        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(icmpfilter)/sizeof(sock_filter);
    }
    else if(fType == IGMPFILTER) {
        // Filter IGMP Packets
        sock_filter igmpfilter[] = {
            // Instructions
            BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 12),                 // fixed offset = ethernet hardware address
            BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   ETH_P_IP,     0, 7), // eth hardware addr != IP, skip next 7 instruc
            BPF_STMT(BPF_LD  + BPF_B    + BPF_ABS, 23),                 // offset = IP protocol
	        BPF_JUMP(BPF_JMP + BPF_JEQ  + BPF_K,   IPPROTO_IGMP, 0, 5), // protocol != IGMP, skip next 5 instruc
	        BPF_STMT(BPF_LD  + BPF_H    + BPF_ABS, 20),                 // offset = flags, fragment offset   
            BPF_JUMP(BPF_JMP + BPF_JSET + BPF_K,   0x1fff,       3, 0), // ((R,DF,MF = 0, fragOff = 8191(MAX)) & Current Flags, FOff),
                                                                        // true, skip next 3 instruc
            BPF_STMT(BPF_LDX + BPF_B    + BPF_MSH, 14),                 // offset = IP version + IP header length
                                                                        // load IP header len(14) into register
            BPF_STMT(BPF_LD  + BPF_H    + BPF_IND, 14),                 // variable offset = IGMP type
            // Accept
            BPF_STMT(BPF_RET + BPF_K,     (u_int)-1),                   // return IGMP packet
            // Drop
    	    BPF_STMT(BPF_RET + BPF_K,     0),                           // return null
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(igmpfilter)))) {
            std::perror("malloc");
            return -1;
        }

        // Copy In
        std::memcpy(s_filter, &igmpfilter, sizeof(igmpfilter));
 
        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(igmpfilter)/sizeof(sock_filter);
    }
    else if(fType == TCPFILTER) { // wifi
        cuchar_cptr  tempip = (cuchar_cptr)"192.168.0.4";
        unsigned char networkIP[sizeof(in_addr)];

        // Zero Out
        std::memset(networkIP, 0, sizeof(networkIP));

        // Convert IP To Network Order
        if(inet_pton(AF_INET, (const char*)tempip, networkIP) == -1) {
            std::perror("inet_pton");
            return false;
        }

        // Filter TCP Packets
        sock_filter tcpfilter[] = {
            // Little Endian Load Radiotap Length
	        BPF_STMT(BPF_LD   | BPF_B   | BPF_ABS, 2), // load lower byte into A
	        BPF_STMT(BPF_MISC | BPF_TAX,           0), // put into X (== index reg)
	        BPF_STMT(BPF_LD   | BPF_B   | BPF_ABS, 3), // load upper byter into A
	        BPF_STMT(BPF_ALU  | BPF_LSH | BPF_K,   8), // left shift it by 8
	        BPF_STMT(BPF_ALU  | BPF_OR  | BPF_X,   0), // OR with X
	        BPF_STMT(BPF_MISC | BPF_TAX,           0), // put result into X
            
            // Let Only Management Frames Through
          /*BPF_STMT(BPF_LD  | BPF_B   | BPF_IND, 0),       // load lower frame ctrl byte
            BPF_STMT(BPF_ALU | BPF_AND | BPF_K,   0xF),     // mask off frame type and version
            BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K,   0, 0, 1), // accept if MGMT(0x00) frame*/
	      
            // Drop Non-Data Frames And WDS Frames
            BPF_STMT(BPF_LD  | BPF_B   | BPF_IND, 0),       // load lower frame ctrl byte
            BPF_STMT(BPF_ALU | BPF_AND | BPF_K,   0x0c),    // mask off QOS bit
            BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K,   8, 0, 4), // drop non-data frames
            BPF_STMT(BPF_LD  | BPF_B   | BPF_IND, 0),       // load upper frame ctrl byte
            BPF_STMT(BPF_ALU | BPF_AND | BPF_K,   0x03),    // mask off toDS and fromDS
            BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K,   3, 1, 0), // drop WDS(0x03) frames
          
            // Add Header Length To Index
            BPF_STMT(BPF_LD   | BPF_B   | BPF_IND, 0),    // load lower frame ctrl byte
            BPF_STMT(BPF_ALU  | BPF_AND | BPF_K,   0x80), // mask off QOS bit
            BPF_STMT(BPF_ALU  | BPF_RSH | BPF_K,   6),    // right shift it by 6 to give 0 or 2
            BPF_STMT(BPF_ALU  | BPF_ADD | BPF_K,   24),   // add data frame header length
            BPF_STMT(BPF_ALU  | BPF_ADD | BPF_X,   0),    // add index, was start of 802.11 header
            BPF_STMT(BPF_MISC | BPF_TAX,           0),    // move to index, start of LLC

            // Accept Only LLC LSAP SNAP Extension Packets
            BPF_STMT(BPF_LD  | BPF_W   | BPF_IND, 0),                // load dsap, lsap, ctrl LLCs, SNAP oui 1st octet
            BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K,   0xAAAA0300, 0, 1), // accept only SNAP extension

            // Accept Only IP Protocol Packets
            BPF_STMT(BPF_LD  | BPF_W   | BPF_IND, 4),                // oui, last 2 octets and ether_type SNAP fields
            BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K,   0x00000800, 0, 3), // accpet only IP packets

            // Accpet Only TCP Packets
            BPF_STMT(BPF_LD  | BPF_B   | BPF_IND, 17),                // load IP protocol
	        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K,   IPPROTO_TCP, 0, 1), // accept only TCP

            // Check IP Address
            //BPF_STMT(BPF_LD  | BPF_W   | BPF_IND, 20), // load IP source address
            //BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K,   0x27F7E6B, 0, 1),

            // Accept
            BPF_STMT(BPF_RET | BPF_K, (u_int)-1), // return packet
            // Drop
	        BPF_STMT(BPF_RET | BPF_K, 0),         // return null
        };

        // Allocate Filter
        if(!(s_filter = (sock_filter*)std::malloc(sizeof(tcpfilter)))) {
            std::perror("malloc");
            return -1;
        }
    
        // Copy In
        std::memcpy(s_filter, &tcpfilter, sizeof(tcpfilter));

        // Initialize
        fprog.filter = s_filter;
        fprog.len    = sizeof(tcpfilter)/sizeof(sock_filter);
    }
    else
        return -1;

    // Attach Linux Packet Filter
    if(setsockopt(sfd, SOL_SOCKET, SO_ATTACH_FILTER, &fprog, sizeof(fprog))) {
        std::perror("attach_filter: setsockopt - SO_ATTACH_FILTER");
        return -1;
    }

    // Success
    return 0;
}

int Sniffer::raw_filter(int sfd, cuchar_cptr mac_addr) { // filter via tcpdump output
    // Declarations
    uint32_t    mac0 = 0,
                mac1 = 0;
    sock_filter BPF_code[13];
    sock_fprog  filter;

    // Zero Out
    std::memset(&mac0,    0, sizeof(uint32_t));
    std::memset(&mac1,    0, sizeof(uint32_t));
    std::memset(BPF_code, 0, sizeof(sock_filter));   
    std::memset(&filter,  0, sizeof(sock_fprog));

    // Copy MAC Address In
    std::memcpy(&mac1, &mac_addr[2], 4);
    std::memcpy(&mac0, &mac_addr[0], 2);
    
    // Initialize
    mac1 = htonl(mac1);
    mac0 = htons(mac0);
    
    // -s 0 ether host AA:BB:CC:DD:EE:FF or ether broadcast
    BPF_code[0]  = (sock_filter) { 0x20, 0, 0, 0x00000008 }; // un-extended format
    BPF_code[2]  = (sock_filter) { 0x28, 0, 0, 0x00000006 };
    BPF_code[3]  =  sock_filter  { 0x15, 7, 0, mac0       }; // extended format std=c++11
    BPF_code[4]  =  sock_filter  { 0x20, 0, 0, 0x00000002 };
    BPF_code[5]  =  sock_filter  { 0x15, 0, 2, mac1       };
    BPF_code[6]  =  sock_filter  { 0x28, 0, 0, 0x00000000 };
    BPF_code[7]  =  sock_filter  { 0x15, 3, 4, mac0       };
    BPF_code[8]  =  sock_filter  { 0x15, 0, 3, 0xffffffff };
    BPF_code[9]  =  sock_filter  { 0x28, 0, 0, 0x00000000 };
    BPF_code[10] =  sock_filter  { 0x15, 0, 1, 0x0000ffff };
    BPF_code[11] =  sock_filter  { 0x6,  0, 0, 0x0000ffff };
    BPF_code[12] =  sock_filter  { 0x6,  0, 0, 0x00000000 };

    // Initialize Members
    filter.len    = 13;
    filter.filter = BPF_code;
	
    // Attch Linux Packet Filter
    if(setsockopt(sfd, SOL_SOCKET, SO_ATTACH_FILTER, &filter, sizeof(filter))) {
	    std::perror("setsockopt - SO_ATTACH_FILTER");
	    return -1;
    }

    // Success
    return 0;
}

// Constant Member Functions
const unsigned Sniffer::getDropedP() const {
    tpacket_stats stats;
    int len = 0;
    if(getsockopt(sfd, SOL_PACKET, PACKET_STATISTICS, &stats, (socklen_t*)&len)) {
        std::perror("getsockopt = PACKET_STATISTICS");
	    return -1;
	}

   return stats.tp_drops;
}

const unsigned Sniffer::getFreezeQCount() const { // only for V3 Packet
    tpacket_stats_v3 stats;
    if(getsockopt(sfd, SOL_PACKET, PACKET_STATISTICS, &stats, (socklen_t*)sizeof(stats))) {
        std::perror("getsockopt = PACKET_STATISTICS");
	    return -1;
	}

   return stats.tp_freeze_q_cnt;
}

void Sniffer::def_printSniffer() const {
    std::cout << CLRSCRN
              << "\nSniffed: "
              << "\n         "
              << getMGMT()        << " Wifi MGMT, "
              << getCTRL()        << " Wifi CTRL, "
              << getData()        << " Wifi Data, "
              << getQOS()         << " Wifi QOS Data"
              << "\n         "                     
              << getEXT()         << " Wifi EXT, "
              << getWDS()         << " Wifi WDS"
              << "\n         "             
              << getDataCtrl()    << " Wifi Data Control, "
              << getQOSCtrl()     << " Wifi QOS Data Control"
              << "\n         "
              << getDataEncrypt() << " Wifi Encrypted(PAE/ARP/IP/TCP...)"
              << "\n         "             
              << getARP()         << " ARP, "
              << getPAE()         << " PAE, "
              << getTDLS()        << " TDLS, "
              << getSTP()         << " STP"
              << "\n         "
              << getTCP()         << " TCP, "
              << getUDP()         << " UDP, "
              << getSCTP()        << " SCTP, "
              << getICMP()        << " ICMP, "
              << getIGMP()        << " IGMP"
              << "\n         "
              << getOtherDataLink()  << " Other Data-Link "
              << "\n         "
              << getOtherNetwork()   << " Other Network "
              << "\n         "
              << getOtherTransport() << " Other Transport"
              << "\n         "
              << RED   << getLocalStoredDrop()       << NF << " Dropped Packets "
              << RED   << getLocalStoredIncomplete() << NF << " Incomplete Packets"
              << "\n         "
              << GREEN << getTotalP()                << NF << " Total Packets"
              << "\n         "
              << GREEN << getTotalB()                << NF << " Total Bytes"
              << "\n         "
              << GREEN << getRxRingOffset()          << NF << " RX Ring Offset"
              << std::endl; // flush n' newline
}

// Mutator Member Functions
bool Sniffer::createSniffer(c_string packetType, const in_port_t port, c_bool rfmon, c_bool promisc,
                            time_t secs, suseconds_t usecs) {
    // Declarations
    sock_filter     s_filter;
    sock_fprog      fprog;
    sockaddr_ll     sll;
    ifreq           ifr;
    iwreq           iwr;
    hwtstamp_config hwconfig;
    unsigned        fType = 0;
    
    // Zero Out Data
    std::memset(&sll,      0, sizeof(sll));
    std::memset(&ifr,      0, sizeof(ifr));
    std::memset(&iwr,      0, sizeof(iwr));
    std::memset(&old_iwr,  0, sizeof(old_iwr));
    std::memset(&old_ifr,  0, sizeof(old_ifr));
    std::memset(&s_filter, 0, sizeof(s_filter));
    std::memset(&fprog,    0, sizeof(fprog));
    std::memset(&treq,     0, sizeof(treq));
	std::memset(&hwconfig, 0, sizeof(hwconfig));

    // Create Interface
    int fd = add_iface(iface);
    if(fd == -1)
        return false;
    
    // Create RAW Socket
    if((sfd = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL))) == -1) {
        std::perror("socket");
        return false;
    }

    // Get Hardware Address
    std::strncpy(ifr.ifr_name, iface, IFNAMSIZ); // copy in interface device   
    if(ioctl(sfd, SIOCGIFHWADDR, &ifr) == -1) {
        std::perror("createSniffer: ioctl - SIOCGIFHWADDR");
        return false;
    }

    // Spoof Our Hardware(MAC) Adrress
    ++ifr.ifr_hwaddr.sa_data[0]; ++ifr.ifr_hwaddr.sa_data[1]; 
    ++ifr.ifr_hwaddr.sa_data[2]; ++ifr.ifr_hwaddr.sa_data[3];
    ++ifr.ifr_hwaddr.sa_data[4]; ++ifr.ifr_hwaddr.sa_data[5];
    
    std::memcpy(smac, &ifr.ifr_hwaddr.sa_data, ETH_ALEN); // copy in
    
    // Get Interface Index
    std::strncpy(ifr.ifr_name, iface, IFNAMSIZ); // copy in interface device
    if(ioctl(sfd, SIOCGIFINDEX, &ifr) == -1) {
        std::perror("createSniffer: ioctl - SIOCGIFINDEX");
        return false;
    }

    // Set Up Socket Link-Layer Address
    sll.sll_ifindex  = ifr.ifr_ifindex;
    sll.sll_family   = AF_PACKET;
    sll.sll_protocol = htons(ETH_P_ALL);
    sll.sll_hatype   = htons(ARPHRD_ETHER);
    sll.sll_pkttype  = PACKET_OTHERHOST;
    sll.sll_halen    = ETH_ALEN;
    std::memcpy(&sll.sll_addr, smac, ETH_ALEN); // copy in

    // Bind RAW Socket
    if(bind(sfd, (sockaddr*)&sll, sizeof(sll))) {
        std::perror("bind");
        return false;
    }
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////doesnt work with eth0's
    // Save Current Interface Mode
    if(rfmon) {
        std::strncpy(old_iwr.ifr_name, iface, IFNAMSIZ); // copy in interface device
        if(ioctl(sfd, SIOCGIWMODE, &old_iwr) == -1) {
            std::perror("createSniffer: ioctl - SIOCGIWMODE");
            return false;
        }
    }

    // Get Current Interface Flags
    std::strncpy(ifr.ifr_name, iface, IFNAMSIZ); // copy in interface device
    if((ioctl(sfd, SIOCGIFFLAGS, &ifr) == -1)) {
	    std::perror("createSniffer: ioctl - SIOCGIFFLAGS");
	    return false;
	}

    // Save Current Interface Flags
    old_ifr.ifr_flags = ifr.ifr_flags;

    // Check If Curent Interface Is Up
    if((ifr.ifr_flags & IFF_UP & IFF_BROADCAST & IFF_RUNNING) != ifr.ifr_flags) {
        // Or In Up, Broadcast, Running
        ifr.ifr_flags |= IFF_UP | IFF_BROADCAST | IFF_RUNNING;

        // Set Interface Flags   
        if(ioctl(sfd, SIOCSIFFLAGS, &ifr) == -1) {
            std::perror("createSniffer: : ioctl - SIOCSIFFLAGS");
            return false;
        }
    }

    // Set Up Time Outs
    timeval receive_timeout;
    receive_timeout.tv_sec  = secs;
    receive_timeout.tv_usec = usecs; // microseconds
    if(setsockopt(sfd, SOL_SOCKET, SO_RCVTIMEO, &receive_timeout, sizeof(receive_timeout))) {
        std::perror("createSniffer: setsockopt - SO_RCVTIMEO");
        return false;
    }

    // Set Packet Version
    int v = TPACKET_V2;
    if(setsockopt(sfd, SOL_PACKET, PACKET_VERSION, &v, sizeof(v))) {
        std::perror("createSniffer: setsockopt - PACKET_VERSION");
        return false;
    }

    // Set Up Packet Fanout Load Balancing
    /*int fanout_id   = getpid() & 0xffff,
        fanout_type = PACKET_FANOUT_HASH, // or use PACKET_FANOUT_LB
        fanout_arg  = fanout_id | (fanout_type << 16);
	if(setsockopt(sfd, SOL_PACKET, PACKET_FANOUT, &fanout_arg, sizeof(fanout_arg))) {
	    std::perror("setsockopt - PACKET_FANOUT");
		return false;
	}*/
   
    // Set Up Receiving Ring Sizes, Used For Both RX And TX
    treq.tp_block_size       = RING_FRAMES * getpagesize();
    treq.tp_block_nr         = 1;   
    treq.tp_frame_size       = getpagesize();
    treq.tp_frame_nr         = RING_FRAMES;
    treq.tp_retire_blk_tov   = 60;                    // 60 millisecond wait, V3
    treq.tp_feature_req_word = TP_FT_REQ_FILL_RXHASH; // fill via skbuffs packet hash, V3

    // Sanity Check Our Frames And Blocks
    if((treq.tp_frame_size <= TPACKET2_HDRLEN) || (treq.tp_frame_size % TPACKET_ALIGNMENT)
                                               || (treq.tp_block_size % treq.tp_frame_size)) {
        std::cerr << "\ncreateSniffer: Sanity Checks";
        return false;
    }
    
    // Attach Packet Rings
    if(setsockopt(sfd, SOL_PACKET, PACKET_RX_RING, &treq, sizeof(treq)) == -1) { // RX
        std::perror("createSniffer: setsockopt - PACKET_RX_RING");
        return false;
    }
    if(setsockopt(sfd, SOL_PACKET, PACKET_TX_RING, &treq, sizeof(treq)) == -1) { // TX
        std::perror("createSniffer: setsockopt - PACKET_RX_RING");
        return false;
    }

    // Memory Map For Semi-Zero Copy, RX And TX Will Be Asymetric
    if((ring = (unsigned char*)mmap(NULL, ((treq.tp_block_size * treq.tp_block_nr) * 2), // times 2, both RX and TX
                                    PROT_READ | PROT_WRITE, MAP_SHARED | MAP_LOCKED, sfd, 0)) == MAP_FAILED) {
        std::perror("createSniffer: mmap");
        return false;
    }

    // Set Up CPU Affinity
    pid_t cpuid = 0;       // cpu core 0  
    cpu_set_t mask;
    CPU_ZERO(&mask);       // zero
    CPU_SET(cpuid, &mask); // set ID
    if(sched_setaffinity(cpuid, sizeof(mask), &mask)) {
        std::perror("createSniffer: sched_setaffinity");
        return false;
    }
   
    // Set Up Monitor Mode
    if(rfmon)   
        if(rfmon_up(iface, sfd))
            return false;

    // Set Promiscous Mode
    if(promisc)
        if(promisc_up(iface, sfd))
            return false;

    // Process Packet Filtering Choice
    if     (packetType == "-ARP" ) {
        fType = ARPFILTER;
    }
    else if(packetType == "-ALL" ) {
        fType = PROMISCFILTER;
    }
    else if(packetType == "-IP"  ) {
        fType = IPFILTER;
    }
    else if(packetType == "-ICMP") {
        fType = ICMPFILTER;
    }
    else if(packetType == "-IGMP") {
        fType = IGMPFILTER;
    }
    else if(packetType == "-TCP" ) {
        fType = TCPFILTER;
        PORT  = port;
    }
    else if(packetType == "-UDP" ) {
        fType = UDPFILTER;
        PORT  = port;
    }
    else if(packetType == "-SCTP") {
        fType = SCTPFILTER;
        PORT  = port;
    }
    else if(packetType == "-MAC")
        fType = MACFILTER;
    else
        return false;

    // Set Up Filter
    if(attach_filter(iface, smac, sfd, fType))
        return false;

    // Success
    return true;
}

int Sniffer::sniffPackets() {   
    // Grab Packet
    tpacket2_hdr *packet = (tpacket2_hdr*)process_rx();
    if(!packet)
        return -1;

    // Process Packet
    packet_switch(packet, packet->tp_snaplen);

    // Release Packet
    process_rx_release();

    // Success
    return packet->tp_len;
}

int Sniffer::closeSniffer(c_bool monOff) {
    // Close Radio Frequency Mode, Promiscous, Memory Map
    if(monOff) // only close if supplie monOff Flag
        if(rfmon_down(iface, sfd))
            return -1;
    if(promisc_down(iface, sfd))
        return -2;
    if(map_destruct())
        return -3;

    // Flush Out Stream To File
    ofs.flush();

    // Success
    return 0;
}

// Private Member Functions
void* Sniffer::process_rx() {
    // Set Up Polling
    pollfd pfd;
    pfd.fd      = sfd;
    pfd.events  = POLLIN | POLLRDNORM | POLLERR;
    pfd.revents = 0;

    // Fetch Our RX Frame
    volatile tpacket2_hdr *header __aligned_tpacket = (tpacket2_hdr*)(ring + (rxring_offset * getpagesize()));

    // Sanity Check Our Frame
    assert(!(((unsigned long)header)&(getpagesize()-1)));

    // Check For Consumption 
    if(!(header->tp_status & TP_STATUS_USER)) { // check if kernel owns it, TP_STATUS_KERNEL(0)
        int ret = poll(&pfd, 1, -1); // wait(poll)
        if(ret == -1) {
            if(errno != EINTR) {     // harder error
                std::perror("poll");
                return (void*)-1;
            }
            return NULL;             // let user know signal interuption
        }
    }

    // Check Frame Metadata
    if((header->tp_status & TP_STATUS_COPY)) { // too long so truncated
        ++incompleteC;
        //return (void*)-1;
    }
    if((header->tp_status & TP_STATUS_LOSING)) {
        ++dropC;
        //return (void*)-1;
    }

    // Success, Return Packet
    return (void*)header;
}

void* Sniffer::process_tx() {
    // Set Up Polling
    pollfd pfd;
    pfd.fd      = sfd;
    pfd.events  = POLLOUT;
    pfd.revents = 0;

    // Fetch Our TX Frame
    tpacket2_hdr *header __aligned_tpacket = (tpacket2_hdr*)((ring + (treq.tp_block_size * treq.tp_block_nr))
                                                                   + (txring_offset      * getpagesize()));

    // Sanity Check Our Frame
    assert(!(((unsigned long)header)&(getpagesize()-1)));

    // Check For Availability
    if(header->tp_status & ~TP_STATUS_AVAILABLE) {/////////////////////////////////////////////////////////////////////////? check
        int ret = poll(&pfd, 1, -1); // wait(poll)
        if(ret == -1) {
            if(errno != EINTR) {     // harder error
                std::perror("poll");
                return (void*)-1;
            }
            return NULL;             // let user know signal interuption
        }
    }

    // Success, Return Packet
    return (void*)header;
}

void Sniffer::process_rx_release() {
    // Re-Fetch Our RX Frame
    volatile tpacket2_hdr *header __aligned_tpacket = (tpacket2_hdr*)(ring + (rxring_offset * getpagesize()));

    // Grant Kernel Status   
    header->tp_status = TP_STATUS_KERNEL; // flush status

    // Update Consumer Pointer
    rxring_offset = (rxring_offset + 1) & (RING_FRAMES - 1);
}

void Sniffer:: process_tx_release(c_uint len) {
    // Re-Fetch Our TX Frame
    tpacket2_hdr *header __aligned_tpacket = (tpacket2_hdr*)((ring + (treq.tp_block_size * treq.tp_block_nr))
                                                                   + (txring_offset      * getpagesize()));

    // Grant Send Status
    header->tp_len    = len;
    header->tp_status = TP_STATUS_SEND_REQUEST;

    // Update Consumer Pointer
    txring_offset = (txring_offset + 1) & (RING_FRAMES - 1);
}

inline unsigned Sniffer::nxt_pow_two(c_uint n) { // pagesize ^ 2, for block_size, V3 packet
    // Declarations
    unsigned pN = n;

    // Get Next Power Of Two
    --pN;
    pN |= pN >> 1,
    pN |= pN >> 2;
    pN |= pN >> 4;
    pN |= pN >> 8;
    pN |= pN >> 16;
    ++pN;
  
    // Success
    return n;
}

void Sniffer::header_dump(cuchar_cptr buf, c_uint len) {
    // Temp Buffer
    const unsigned P_LEN = len + 1; // null term
    char temp[P_LEN];

    // Zero Out
    std::memset(temp, 0, P_LEN);

    // Print Total Bytes
    ofs << "\nTotal Bytes: " << len;

    // Newline
    ofs << '\n';

    for(std::size_t i = 0; i < len; ++i) {
        // Print Hex Interpretation
        std::snprintf(temp, P_LEN, "%2X ", buf[i]);
        ofs << temp;

        // Check Hex Line Cutoff
        if((i % 16) == 15 || i == len-1) {
            // Line Up Spacing of Last Line of Hex
            for(std::size_t j = 0; j < 15 - (i % 16); ++j)
                ofs << "   ";

            // Divider Bar Between Hex and Readable Form
            ofs << "| ";
            
            // Decode Into Human Readable Form
            for(std::size_t j = (i - (i % 16)); j <= i; ++j) {
                unsigned char c = buf[j];
                if((c > 31) && (c < 127)) // readable ASCII
                    ofs << c;
                else                      // unreadable ASCII
                    ofs << '.';
            }
            
            // Newline
            ofs << '\n';
        }
    }
}

void Sniffer::readable_dump(cuchar_cptr buf, c_uint len) {
    // Temp Buffer
    char *rdump = (char*)buf;

    // Newline
    ofs << '\n';

    // Decode Into Human Readable Form
    for(std::size_t i = 0; i < len; ++i) {
        unsigned char c = rdump[i];
        if((c > 0) && (c < 127)) // readable ASCII
            ofs << c;            // rofs for seperate file output
    }

    // Newline
    ofs << '\n';
}

void Sniffer::packet_switch(const tpacket2_hdr* const packet, c_uint len) {
    // Declarations
    sockaddr_ll *sll = (sockaddr_ll*)((cuchar_cptr)packet + (TPACKET2_HDRLEN - sizeof(sockaddr_ll))); /////////make sure sll and all othe pointers const???????BELOW
    std::time_t  t   = std::time(0);

    // Debug, Prints Whole Packet Header Dump Before, TPacket and All
    if(debugFlag) {
        ofs << "\n\nFull Hex Dump For Packet Below, debug mode";
        header_dump((cuchar_cptr)packet, packet->tp_mac + len);
    }

    // Process Hardware Type
    switch(sll->sll_hatype) { /////////////////////////////////////////////////////get rid of
    case ARPHRD_FCPP: { // Fibrechannel
        ofs << "\n\n\n*****************************FCPP Frame******************************"
            << "\n\nFibrechannel Point-to-Point Frame Time Stamp: " << std::ctime(&t);

        // Print Headers
        printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN);
        printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));

        // Dump Data Packets
        ofs << "\n~~~Data Dump~~~";
        ofs << "\nTPacket Header Dump(pre-pended)";
        header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
        ofs << "\nSocket Address Link Layer Header(pre-pended)";
        header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
        ofs << "\nPayload Dump";
        header_dump((cuchar_cptr)packet + packet->tp_mac, len); // try to dump
            
        ofs << "\n***********************************************************************";

        // Update Totals
        ++otherDataLinkC;
        ++totalPC;
        totalBC += len;
        break;
    }
    case ARPHRD_NETROM: { // un-comment to see if real packet or 0's are comming in, 0's mean wire is empty /////////////////////////////////get rid of
      /*ofs << "\n\n\n**************************KA9Q Tunnel Frame****************************" // 0 type
            << "\nKA9Q: NET/ROM Pseudo Frame Time Stamp: " << std::ctime(&t);

        // Print Headers
        printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
        printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));

        // Dump Data Packets
        ofs << "\n~~~Data Dump~~~";
        ofs << "\nTPacket Header Dump(pre-pended)";
        header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
        ofs << "\nSocket Address Link Layer Header(pre-pended)";
        header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
        ofs << "\nPayload Dump";
        header_dump((cuchar_cptr)packet + packet->tp_mac, len); // try to dump
            
        ofs << "\n***********************************************************************";

        // Update Totals
        ++otherDataLinkC;
        ++totalPC;
        totalBC += len;*/
        break;
    }
    case ARPHRD_IEEE80211: { // Fibrechannel
        ofs << "\n\n\n****************************802.11 Frame*******************************"
            << "\n802.11 Frame Time Stamp: " << std::ctime(&t)
            << "\n~~~Data Dump~~~";
        header_dump((cuchar_cptr)packet + packet->tp_mac, len); // try to dump
        ofs << "\n***********************************************************************";
        ++otherDataLinkC;
        ++totalPC;
        totalBC += len;
        break;
    }
    case ARPHRD_IEEE80211_PRISM: { // Fibrechannel
        ofs << "\n\n\n************************802.11 Prism Frame*****************************"
            << "\n802.11 Prism Frame Time Stamp: " << std::ctime(&t)
            << "\n~~~Data Dump~~~";           
        header_dump((cuchar_cptr)packet + packet->tp_mac, len); // try to dump
        ofs << "\n***********************************************************************";           
        ++otherDataLinkC;
        ++totalPC;
        totalBC += len;
        break;
    }
    case ARPHRD_IEEE80211_RADIOTAP: { // Fibrechannel
        // Declarations, 1st Round
        const ie80211_rtaphdr  *rtap         = (ie80211_rtaphdr*) ((cuchar_cptr)packet + packet->tp_mac);
        const u_ieee80211_hdrs *ie80211_un   = (u_ieee80211_hdrs*)((cuchar_cptr)rtap   + le16toh(rtap->it_len)); // union
        unsigned char          *ie80211_Buf  = NULL; // opaque ieee80211 buffer
        std::size_t             ie80211_Size = 0;    // opaque ieee80211 buffer size
        ieee80211_fcs_hdr *fcs = (ieee80211_fcs_hdr*)((cuchar_cptr)rtap + (len-4));

        // Process IEEE80211 Frame Type To Set Opaque Buffer And Size
        switch(GetFrameType(ie80211_un)) {
        case WIFI_MGMT_FRAME: // Management Frame
            ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_mgmt;
            ie80211_Size = sizeof(ie80211_un->ieee80211_mgmt);
            break;
        case WIFI_CTRL_FRAME: // Control Frames
            // Process IEEE80211 Frame Subtype
            switch(GetFrameSubType(ie80211_un)) {
            case WIFI_CTS:         // Clear To Send
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_cts;
                ie80211_Size = sizeof(ie80211_un->ieee80211_cts); /////////////////////////////////////////////////use actual ieee80211_cts_hdr in size ????????????????????????
                break;
            case WIFI_RTS:         // Request To Send
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_rts;
                ie80211_Size = sizeof(ie80211_un->ieee80211_rts);
                break;
            case WIFI_PSPOLL:      // Power-Save Poll
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_pspoll;
                ie80211_Size = sizeof(ie80211_un->ieee80211_pspoll);
                break;
            case WIFI_ACK:         // Acknowledgment
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_ack;
                ie80211_Size = sizeof(ie80211_un->ieee80211_ack);
            case WIFI_CFEND:       // Contention Free End
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_cfend;
                ie80211_Size = sizeof(ie80211_un->ieee80211_cfend);
                break;
            case WIFI_CFEND_CFACK: // Contention Free End + Contention Free Acknowledgment
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_cfendack;
                ie80211_Size = sizeof(ie80211_un->ieee80211_cfendack);
                break;
            case WIFI_BACK:        // Block Acknowledgment
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_back;
                ie80211_Size = sizeof(ie80211_un->ieee80211_back);
                break;
            case WIFI_BACK_REQ:    // Block Acknowledgment Request
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_backreq;
                ie80211_Size = sizeof(ie80211_un->ieee80211_backreq);
                break;
            case WIFI_CTL_EXT:     // Control Wrapper EXT (802.11n)
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_ctrlext;
                ie80211_Size = sizeof(ie80211_un->ieee80211_ctrlext);
                break;
            default:               // Unknown Control Frame
                ////////////////////////////////////////////////////////////////////////////////////////////
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_rts;
                ie80211_Size = sizeof(ie80211_un->ieee80211_rts);
                break;
            }
            break;
        case WIFI_DATA_FRAME: // Data Frames
            // Process Regular Data Or QOS Data Frame
            if(GetFrameSubType(ie80211_un) == WIFI_QOS_DATA           || // QOS
               GetFrameSubType(ie80211_un) == WIFI_QOS_DATA_CFACK     ||
               GetFrameSubType(ie80211_un) == WIFI_QOS_DATA_CFPOLL    ||
               GetFrameSubType(ie80211_un) == WIFI_QOS_DATA_CFACKPOLL ||
               GetFrameSubType(ie80211_un) == WIFI_QOS_NULL           ||
               GetFrameSubType(ie80211_un) == WIFI_QOS_CFACK          ||
               GetFrameSubType(ie80211_un) == WIFI_QOS_CFPOLL         ||
               GetFrameSubType(ie80211_un) == WIFI_QOS_CFACKPOLL) {
                // Process ToDS and FromDS Bits For Correct Address Count
                if(GetToDS(ie80211_un) && GetFromDS(ie80211_un)) { // 1 1, WDS 4 addrs
                    ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_qos_4;
                    ie80211_Size = sizeof(ie80211_un->ieee80211_qos_4);
                }
                else { // 0 1 or 1 0 or 0 0, 3 addrs
                    ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_qos_3;
                    ie80211_Size = sizeof(ie80211_un->ieee80211_qos_3);
                }
            }
            else { // regular
                // Process ToDS and FromDS Bits For Correct Address Count
                if(GetToDS(ie80211_un) && GetFromDS(ie80211_un)) { // 1 1, WDS 4 addrs
                    ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_4;
                    ie80211_Size = sizeof(ie80211_un->ieee80211_4);
                }
                else { // 0 1 or 1 0 or 0 0, 3 addrs
                    ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_3;
                    ie80211_Size = sizeof(ie80211_un->ieee80211_3);
                }
            }
            break;
        case WIFI_EXT_FRAME:
            // Process ToDS and FromDS Bits For Correct Address Count, *Kinda-Guess On Type
            if(GetToDS(ie80211_un) && GetFromDS(ie80211_un)) { // 1 1, WDS 4 addrs
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_4;
                ie80211_Size = sizeof(ie80211_un->ieee80211_4);
            }
            else { // 0 1 or 1 0 or 0 0, 3 addrs
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_3;
                ie80211_Size = sizeof(ie80211_un->ieee80211_3);
            }

            // Check If Size To Large And Need A CTRL 2 Address Structure Type
            if((len - le16toh(rtap->it_len) - ie80211_Size)) { // not null
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_rts;
                ie80211_Size = sizeof(ie80211_un->ieee80211_rts);
            }
            break;
        default: // Unknown Frame, check online in reserves for others          
            // Process ToDS and FromDS Bits For Correct Address Count, *Kinda-Guess On FType
            if(GetToDS(ie80211_un) && GetFromDS(ie80211_un)) { // 1 1, WDS 4 addrs
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_4;
                ie80211_Size = sizeof(ie80211_un->ieee80211_4);
            }
            else { // 0 1 or 1 0 or 0 0, 3 addrs
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_3;
                ie80211_Size = sizeof(ie80211_un->ieee80211_3);
            }

            // Check If Size To Large And Need A CTRL 2 Address Structure Type
            if((len - le16toh(rtap->it_len) - ie80211_Size)) { // not null
                ie80211_Buf  = (unsigned char*)&ie80211_un->ieee80211_rts;
                ie80211_Size = sizeof(ie80211_un->ieee80211_rts);
            }
            break;
        } // Frame Type Switch End

        // Declarations, 2nd Round
        llc_hdr  *llc  = (llc_hdr*) (ie80211_Buf      + ie80211_Size);
        snap_hdr *snap = (snap_hdr*)((cuchar_cptr)llc + sizeof(llc_hdr));;

        // SLL Always Prints ETH_P_802_2 For ARPHRD_IEEE80211_RADIOTAP, Check LSAP For SNAP
        uint16_t proto = 0;
        if((unsigned)llc->dsap == 170 && (unsigned)llc->ssap == 170 && (unsigned)llc->ctrl1 == 3 &&
            snap->oui[0] == oui_rfc1042[0] && snap->oui[1] == oui_rfc1042[1] && snap->oui[2] == oui_rfc1042[2])
            proto = ntohs(snap->ether_type); // expicitly change for the rest of switch
        else // Our Frame Is Regular MGMT/CTRL/QOS/DATA/EXT/Encrypted, So Process In ETH_P_802_2
            proto = ntohs(sll->sll_protocol);

        // Process Ethernet Protocol
        switch(proto) {
        case ETH_P_802_2: { // LLC, non DIX type
            // Declarations /*catch our regular data and qos, mgmt, qosnodata, datanodata, encrypted, other ouis
            bool mgmt    = false, ctrl = false, dataCtrl = false, data  = false, dEncrypt = false,
                 qosCtrl = false, qos  = false, ext      = false, other = false;
            unsigned pSize = len - le16toh(rtap->it_len) - ie80211_Size;
           
            // Check pSize Wrap Around Errors(underflow on an unsigned integer)
            if(pSize > len) // add however many bytes needed through i, to not wrap
                for(unsigned i = 0; pSize > len; pSize = (len + ++i) - le16toh(rtap->it_len) - ie80211_Size);
            
            // Process Frame, No LLC
            if(GetFrameType(ie80211_un) == WIFI_MGMT_FRAME) { // MGMT
                ofs << "\n\n\n***************************802.11 MGMT Frame***************************"
                    << "\n\n802.11 Management Frame Time Stamp: " << std::ctime(&t);
                mgmt = true;
            }
            else if(GetFrameType(ie80211_un) == WIFI_CTRL_FRAME) { // CTRL
                ofs << "\n\n\n***************************802.11 CTRL Frame***************************"
                    << "\n\n802.11 Control Frame Time Stamp: " << std::ctime(&t);
                ctrl = true;
            }
            /* encrypted check needs to come before data frames to print right **pattern */
            else if(GetPrivacy(ie80211_un)) {
                ofs << "\n\n\n***********************802.11 Encrypted Frame**************************"
                    << "\n\n802.11 Encrypted Frame Time Stamp: " << std::ctime(&t);
                dEncrypt = true;
            }
            else if(GetFrameType(ie80211_un) == WIFI_DATA_FRAME      && // Data
                    (GetFrameSubType(ie80211_un) == WIFI_DATA        ||
                     GetFrameSubType(ie80211_un) == WIFI_DATA_CFACK  ||
                     GetFrameSubType(ie80211_un) == WIFI_DATA_CFPOLL ||
                     GetFrameSubType(ie80211_un) == WIFI_DATA_CFACKPOLL)) {
                ofs << "\n\n\n**************************802.11 Data Frame****************************"
                    << "\n\n802.11 Data Frame Time Stamp: " << std::ctime(&t);
                data = true;
            }
            else if(GetFrameType(ie80211_un) == WIFI_DATA_FRAME    && // No Data, Control Type
                    (GetFrameSubType(ie80211_un) == WIFI_DATA_NULL ||
                     GetFrameSubType(ie80211_un) == WIFI_CFACK     ||
                     GetFrameSubType(ie80211_un) == WIFI_CFPOLL    ||
                     GetFrameSubType(ie80211_un) == WIFI_CFACKPOLL)) {
                ofs << "\n\n\n***********************802.11 Data Control Frame***********************"
                    << "\n\n802.11 Data Control Frame Time Stamp: " << std::ctime(&t);
                dataCtrl = true;
            }
            else if(GetFrameType(ie80211_un) == WIFI_DATA_FRAME         && // QOS Data
                   (GetFrameSubType(ie80211_un) == WIFI_QOS_DATA        ||
                    GetFrameSubType(ie80211_un) == WIFI_QOS_DATA_CFACK  ||
                    GetFrameSubType(ie80211_un) == WIFI_QOS_DATA_CFPOLL ||
                    GetFrameSubType(ie80211_un) == WIFI_QOS_DATA_CFACKPOLL)) {
                ofs << "\n\n\n**********************802.11 QOS Data Frame****************************"
                    << "\n\n802.11 Quality Of Service Data Frame Time Stamp: " << std::ctime(&t);
                qos = true;
            }
            else if(GetFrameType(ie80211_un) == WIFI_DATA_FRAME    && // QOS No Data, Control Type
                   (GetFrameSubType(ie80211_un) == WIFI_QOS_NULL   ||
                    GetFrameSubType(ie80211_un) == WIFI_QOS_CFACK  ||
                    GetFrameSubType(ie80211_un) == WIFI_QOS_CFPOLL ||
                    GetFrameSubType(ie80211_un) == WIFI_QOS_CFACKPOLL)) {
                ofs << "\n\n\n*********************802.11 QOS Data Control Frame*********************"
                    << "\n\n802.11 Quality Of Service Data Control Frame Time Stamp: " << std::ctime(&t);
                qosCtrl = true;
            }
            else if(GetFrameType(ie80211_un) == WIFI_EXT_FRAME) { // Extension
                ofs << "\n\n\n********************802.11 Control Wrapper Frame***********************"
                    << "\n\n802.11 Control Wrapper Extension Frame Time Stamp: " << std::ctime(&t);
                ext = true;
            }
            else { // Unknown Network
                ofs << "\n\n\n************************Other Network Frame****************************"
                    << "\n\nOther Network Frame Time Stamp: " << std::ctime(&t);
                other = true;
            }

            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
            
            // If MGMT Frame, Use Information Element Size
            if(mgmt)
                printIEEE80211((cuchar_cptr)ie80211_Buf, pSize - sizeof(ieee80211_fcs_hdr));
            else
                printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);

            // Print Frame Check Sequence
            //if(mgmt || ctrl || dataCtrl || qosCtrl || data || qos)
                //ofs << "\nFrame Check Sequence: " << le32toh(fcs->fcs) << '\n';
           
            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
            header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
            ofs << "\nieee 802.11 Header Dump";
            header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
            
            // Process Payload Dumping
            if(dEncrypt) {   // encrypted
                ofs << "\nEncrypted Headers + Payload Dump";
                header_dump((cuchar_cptr)llc, pSize);
            }
            else if(other) { // unknown
                ofs << "\nUnknown Payload Dump";
                header_dump((cuchar_cptr)llc, pSize);
            }
            else if(ext) {   // control wrapper, 802.11n
                ofs << "\nCarried Frame + Payload Dump";
                header_dump((cuchar_cptr)llc, pSize);
            }
            else if(mgmt) {  // MGMT, No Payload But Information Elements
                ofs << "\nInformation Elements Dump";
                header_dump((cuchar_cptr)llc, pSize);
            }

            // Dump Frame Check Sequence
            //if(mgmt || ctrl || dataCtrl || qosCtrl || data || qos) {
                //ofs << "\nFrame Check Sequence Dump";
                //header_dump((cuchar_cptr)fcs, sizeof(ieee80211_fcs_hdr));
            //}

            ofs << "\n***********************************************************************";

            // Update Totals
            if(mgmt)
                ++mgmtC;
            else if(ctrl)
                ++ctrlC;
            else if(data)
                ++dataC;
            else if(dataCtrl)
                ++dataCtrlC;
            else if(dEncrypt)
                ++data_encryptC;
            else if(qos)
                ++qosC;
            else if(qosCtrl)
                ++qosCtrlC;
            else if(ext)
                ++extC;
            else
                ++otherNetworkC;
            
            ++totalPC;
            totalBC += len;
            break;
        }
        case ETH_P_IPV6: // IPv6
            // Process IPv6 Below
            /* Fall Trough */
        case ETH_P_IP: { // IPv4
            const iphdr    *ip4H   = (iphdr*)  ((cuchar_cptr)snap + sizeof(snap_hdr));
            const ipv6hdr  *ip6H   = (ipv6hdr*)((cuchar_cptr)snap + sizeof(snap_hdr));
            unsigned short  ip_len = 0;    // opaque buffer size
            unsigned char  *ipH    = NULL; // opaque IP buffer
            unsigned        proto  = 0;    // upper-layer protocol

            // Fill In Correct IP Version, Opaque Buffer, And Size
            if((unsigned)ip4H->version == 4) {
                proto  = (unsigned)ip4H->protocol;
                ip_len = ip4H->ihl * 4; // in 4 byte lengths
                ipH    = (unsigned char*)((iphdr*)((cuchar_cptr)snap + sizeof(snap_hdr)));
            }
            else {
                proto  = (unsigned)ip6H->nexthdr;
                ip_len = sizeof(ipv6hdr);
                ipH    = (unsigned char*)((ipv6hdr*)((cuchar_cptr)snap + sizeof(snap_hdr)));
            }

            // Process IP Protocol
            switch(proto) {
            // RFC 2460 IPv6 More-Than-One Extension Ordering
            // Order 1
            case IPPROTO_HOPOPTS:  // IPv6, conflicts with dummy TCP for IPv4, shouldn't interefere
                break;
            // Order 2 and 8
            case IPPROTO_DSTOPTS:  // IPv6
                break;
            // Order 3
            case IPPROTO_ROUTING:  // IPv6
                break;
            // Order 4
            case IPPROTO_FRAGMENT: // IPv6
                break;
            // Order 5
            case IPPROTO_AH:       // IPv4/IPv6
                break;
            // Order 6
            case IPPROTO_ESP:      // IPv4/IPv6
                break;
            // Order 7
            case IPPROTO_NONE:     // IPv6, no next header(upper protocol)
                break;
            case IPPROTO_MH:       // IPv6
                break;
            case IPPROTO_IPIP:     // IPv4/IPv6, IP-in-IP tunnel
                break;
            case IPPROTO_RSVP:     // IPv4/IPv6
                break;
            case IPPROTO_ICMPV6:   // IPv6
                // Process ICMPv6 Below
                /* Fall Through */
            case IPPROTO_ICMP: {   // IPv4
                const icmphdr *icmpH   = (icmphdr*)   ((cuchar_cptr)ipH   + ip_len);
                cuchar_cptr    pBufICM = (cuchar_cptr)((cuchar_cptr)icmpH + sizeof(icmphdr));
                c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) -
                               sizeof(snap_hdr) - ip_len - sizeof(icmphdr);
                
                ofs << "\n\n\n******************************ICMP Packet******************************"
                    << "\n\nICMP Packet Time Stamp: " << std::ctime(&t);

                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
                printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
                printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
                printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);
                printIP((cuchar_cptr)ipH, ip_len);
                printICMP((cuchar_cptr)icmpH, sizeof(icmphdr));

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
                header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
                ofs << "\nieee 802.11 Header Dump";
                header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
                ofs << "\nLogical Link Layer(LLC) Header Dump";
                header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
                ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
                header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nICMP Header Dump";
                header_dump((cuchar_cptr)icmpH, sizeof(icmphdr));
                ofs << "\nPayload Dump";
                header_dump(pBufICM, pSize);

                ofs << "\n***********************************************************************";

                // Update Totals
                ++icmpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            case IPPROTO_IGMP: {
                const igmphdr *igmpH   = (igmphdr*)   ((cuchar_cptr)ipH   + ip_len);
                cuchar_cptr    pBufIGM = (cuchar_cptr)((cuchar_cptr)igmpH + sizeof(igmphdr));
                c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) -
                               sizeof(snap_hdr) - ip_len - sizeof(igmphdr);

                ofs << "\n\n\n******************************IGMP Packet******************************"
                    << "\n\nIGMP Packet Time Stamp: " << std::ctime(&t);
                
                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
                printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
                printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
                printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);
                printIP((cuchar_cptr)ipH, ip_len);
                printIGMP((cuchar_cptr)igmpH, sizeof(igmphdr));
                
                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
                header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
                ofs << "\nieee 802.11 Header Dump";
                header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
                ofs << "\nLogical Link Layer(LLC) Header Dump";
                header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
                ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
                header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nIGMP Header Dump";
                header_dump((cuchar_cptr)igmpH, sizeof(igmphdr));
                ofs << "\nPayload Dump";
                header_dump(pBufIGM, pSize);

                ofs << "\n***********************************************************************";

                // Update Totals
                ++igmpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            case IPPROTO_TCP: {
                const tcphdr         *tcpH    = (tcphdr*)    ((cuchar_cptr)ipH  + ip_len);
                const unsigned short  tcp_len = tcpH->doff * 4; // in 4 byte lengths
                cuchar_cptr           pBufTCP = (cuchar_cptr)((cuchar_cptr)tcpH + tcp_len);
                c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) - 
                               sizeof(snap_hdr) - ip_len - tcp_len;

                ofs << "\n\n\n******************************TCP  Packet******************************"
                    << "\n\nTCP Packet Time Stamp: "  << std::ctime(&t);

                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
                printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
                printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
                printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);
                printIP((cuchar_cptr)ipH, ip_len);
                printTCP((cuchar_cptr)tcpH, tcp_len);

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
                header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
                ofs << "\nieee 802.11 Header Dump";
                header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
                ofs << "\nLogical Link Layer(LLC) Header Dump";
                header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
                ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
                header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nTCP Header Dump";
                header_dump((cuchar_cptr)tcpH, tcp_len);
                ofs << "\nPayload Dump";
                header_dump(pBufTCP, pSize);

                // Readable Dump
                if(readableDumpFlag) {
                    ofs << "\n~~~Decoded Payload Dump~~~";
                    readable_dump(pBufTCP, pSize);
                }

                ofs << "\n***********************************************************************";

                // Parse Payload
                if(parseDumpFlag) {
                    Parser.fill_parser(pBufTCP, len);
                    Parser.parseFile(toParse);
                    Parser.save_parser(pSavePath);
                    Parser.save_parser(pSavePath);
                }

                // Update Totals
                ++tcpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            case IPPROTO_UDP: {
                const udphdr *udpH    = (udphdr*)    ((cuchar_cptr)ipH  + ip_len);
                cuchar_cptr   pBufUDP = (cuchar_cptr)((cuchar_cptr)udpH + sizeof(udphdr));
                c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) -
                               sizeof(snap_hdr) - ip_len - sizeof(udphdr);

                ofs << "\n\n\n******************************UDP  Packet******************************"
                    << "\n\nUDP Packet Time Stamp: "  << std::ctime(&t);

                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
                printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
                printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
                printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);
                printIP((cuchar_cptr)ipH, ip_len);
                printUDP((cuchar_cptr)udpH, sizeof(udphdr));

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
                header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
                ofs << "\nieee 802.11 Header Dump";
                header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
                ofs << "\nLogical Link Layer(LLC) Header Dump";
                header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
                ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
                header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nUDP Header Dump";
                header_dump((cuchar_cptr)udpH, sizeof(udphdr));
                ofs << "\nPayload Dump";
                header_dump(pBufUDP, pSize);

                // Readable Dump
                if(readableDumpFlag) {
                    ofs << "\n~~~Decoded Payload Dump~~~";
                    readable_dump(pBufUDP, pSize);
                }

                ofs << "\n***********************************************************************";

                // Parse Payload
                if(parseDumpFlag) {
                    Parser.fill_parser(pBufUDP, len);
                    Parser.parseFile(toParse);
                    Parser.save_parser(pSavePath);
                    Parser.save_parser(pSavePath);
                }

                // Update Totals
                ++udpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            case IPPROTO_SCTP: {
                const sctphdr2       *sctpH    = (sctphdr2*)      ((cuchar_cptr)ipH    + ip_len);
                const sctp_chunkhdr2 *sctpHC   = (sctp_chunkhdr2*)((cuchar_cptr)sctpH  + sizeof(sctphdr2));
                cuchar_cptr           pBufSCTP = (cuchar_cptr)    ((cuchar_cptr)sctpHC + sizeof(sctp_chunkhdr2));
                c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) - sizeof(snap_hdr) -
                               ip_len - sizeof(sctphdr2) - sizeof(sctp_chunkhdr2);

                ofs << "\n\n\n******************************SCTP Packet******************************"
                    << "\n\nSCTP Packet Time Stamp: " << std::ctime(&t);

                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
                printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
                printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
                printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);
                printIP((cuchar_cptr)ipH, ip_len);
                printSCTP((cuchar_cptr)sctpH, sizeof(sctphdr2) + sizeof(sctp_chunkhdr2));

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
                header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
                ofs << "\nieee 802.11 Header Dump";
                header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
                ofs << "\nLogical Link Layer(LLC) Header Dump";
                header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
                ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
                header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nSCTP Header Dump";
                header_dump((cuchar_cptr)sctpH, sizeof(sctphdr2));
                ofs << "\nSCTP Chunk Header Dump";
                header_dump((cuchar_cptr)sctpHC, sizeof(sctp_chunkhdr2));
                ofs << "\nPayload Dump";
                header_dump(pBufSCTP, pSize);

                ofs << "\n***********************************************************************";

                // Update Totals
                ++sctpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            default: { // Other Transport Packets
                c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) -
                               sizeof(snap_hdr) - ip_len;               

                ofs << "\n\n\n***********************Other Transport Packet**************************"
                    << "\n\nOther Transport Protocol Packet Time Stamp: " << std::ctime(&t);
                
                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
                printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
                printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
                printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);
                printIP((cuchar_cptr)ipH, ip_len);

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
                header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
                ofs << "\nieee 802.11 Header Dump";
                header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
                ofs << "\nLogical Link Layer(LLC) Header Dump";
                header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
                ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
                header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nUnknown Transport + Payload Dump";
                header_dump((cuchar_cptr)ipH + ip_len, pSize); // try to dump

                ofs << "\n***********************************************************************";

                // Update Totals
                ++otherTransportC;
                ++totalPC;
                totalBC += len;
                break;
            } // Default End
            } // Internet Protocol Switch End
            break;
        }
        case ETH_P_TDLS: { // 802.11z
            c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) - sizeof(snap_hdr);

            ofs << "\n\n\n**************************TDLS 802.11z Frame****************************"
                << "\n\nTunneled Direct Link Setup Frame Time Stamp: " << std::ctime(&t);
            
            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
            printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
            printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
            printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);

            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
            header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
            ofs << "\nieee 802.11 Header Dump";
            header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
            ofs << "\nLogical Link Layer(LLC) Header Dump";
            header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
            ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
            header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
            ofs << "\nPayload Dump";
            header_dump((cuchar_cptr)snap + sizeof(snap_hdr), pSize); // guess on length

            ofs << "\n***********************************************************************";                   

            // Update Totals
            ++tdlsC;
            ++totalPC;
            totalBC += len;
            break;
        }
        case ETH_P_PAE: {
            const EAP_hdr *eap = (EAP_hdr*)((cuchar_cptr)snap + sizeof(snap_hdr));
            c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) -
                           sizeof(snap_hdr) - sizeof(EAP_hdr);           

            ofs << "\n\n\n***************************PAE 802.1X Frame****************************"
                << "\n\nPort Access Entity(802.1X) EAP Frame Time Stamp: " << std::ctime(&t);

            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
            printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
            printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
            printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);
            printIEEE8021X((cuchar_cptr)eap, sizeof(EAP_hdr));
            ofs << "\nFrame Check Sequence: " << le32toh(fcs->fcs) << '\n';

            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
            header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
            ofs << "\nieee 802.11 Header Dump";
            header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
            ofs << "\nLogical Link Layer(LLC) Header Dump";
            header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
            ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
            header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
            ofs << "\nEAP, PAE 802.1X Header Dump";
            header_dump((cuchar_cptr)eap, sizeof(EAP_hdr));
            ofs << "\nPayload Dump";
            header_dump((cuchar_cptr)eap + sizeof(EAP_hdr), pSize);
            ofs << "\nFrame Check Sequence Dump";
            header_dump((cuchar_cptr)fcs, sizeof(ieee80211_fcs_hdr));

            ofs << "\n***********************************************************************";

            // Update Totals
            ++paeC;
            ++totalPC;
            totalBC += len;
            break;
        }
        case ETH_P_ARP: {
            const arphdr2 *arpH = (arphdr2*)((cuchar_cptr)snap + sizeof(snap_hdr));

            ofs << "\n\n\n******************************ARP   Frame******************************"
                << "\n\nARP Frame Time Stamp: " << std::ctime(&t);

            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
            printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
            printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
            printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);
            printARP((cuchar_cptr)arpH, sizeof(arphdr2));
            ofs << "\nFrame Check Sequence: " << le32toh(fcs->fcs) << '\n';

            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
            header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
            ofs << "\nieee 802.11 Header Dump";
            header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
            ofs << "\nLogical Link Layer(LLC) Header Dump";
            header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
            ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
            header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
            ofs << "\nARP Header Dump";
            header_dump((cuchar_cptr)arpH, sizeof(arphdr2));
            ofs << "\nFrame Check Sequence Dump";
            header_dump((cuchar_cptr)fcs, sizeof(ieee80211_fcs_hdr));

            ofs << "\n***********************************************************************";

            // Update Totals
            ++arpC;
            ++totalPC;
            totalBC += len;      
            break;
        }
        case ETH_P_PPP_MP: {
            c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) -
                           sizeof(snap_hdr);
                               
            ofs << "\n\n\n*****************************PPP MP Frame******************************"
                << "\n\nPoint-To-Point Protocol Multilink Frame Time Stamp: " << std::ctime(&t);

            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
            printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
            printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
            printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF);
            
            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
            header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
            ofs << "\nieee 802.11 Header Dump";
            header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
            ofs << "\nLogical Link Layer(LLC) Header Dump";
            header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
            ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
            header_dump((cuchar_cptr)snap, sizeof(snap_hdr));
            ofs << "\nPayload Dump";
            header_dump((cuchar_cptr)snap + sizeof(snap_hdr), pSize);

            ofs << "\n***********************************************************************";
            
            // Update Totals
            ++otherNetworkC;
            ++totalPC;
            totalBC += len;
            break;
        }
        default: { // Other Network Frames/WDS's/OUI's in SNAP/STP Double LLC Encapsulation
            const llc_hdr *llc2 = (llc_hdr*)((cuchar_cptr)snap  + sizeof(snap_hdr)); // Incase Spanning Tree Protocol, 2nd LLC
            const stphdr  *stp  = (stphdr*) ((cuchar_cptr)llc2  + sizeof(llc_hdr));  // STP
            c_uint pSize = len - le16toh(rtap->it_len) - ie80211_Size - sizeof(llc_hdr) - sizeof(snap_hdr);
            bool   other = false, stpFlag = false;
            
            // Check stpPSize Wrap Around Errors
            unsigned stpPSize = pSize - sizeof(llc_hdr) - sizeof(stphdr);
            if(stpPSize > len) // add however many bytes needed through i, to not wrap
                for(unsigned i = 0; stpPSize > len; stpPSize = (len + ++i) - le16toh(rtap->it_len) - ie80211_Size
                        - sizeof(llc_hdr) - sizeof(snap_hdr) - sizeof(llc_hdr) - sizeof(stphdr));

            // Process WDS Frame
            if(GetToDS(ie80211_un) && GetFromDS(ie80211_un)) { // 1 1, WDS Frame Bridge
                if(snap->oui[0] == oui_cisco[0] && snap->oui[1] == oui_cisco[1] && // Cisco OTAP
                   snap->oui[2] == oui_cisco[2] && ntohs(snap->ether_type) == CISCO_OTAP_ETHER_TYPE)
                    ofs << "\n\n\n*********************802.11 OTAP WDS Bridge Frame**********************"
                        << "\n\n802.11 OTAP WDS Bridge Frame Time Stamp: "   << std::ctime(&t);
                else if(snap->oui[0] == oui_cisco2[0] && snap->oui[1] == oui_cisco2[1] && // Cisco Aironet
                        snap->oui[2] == oui_cisco2[2] && ntohs(snap->ether_type) == CISCO_AIRONET_ETHER_TYPE)
                    ofs << "\n\n\n*******************802.11 Aironet WDS Bridge Frame*********************"
                        << "\n\n802.11 Aironet WDS Bridge Frame Time Stamp: "   << std::ctime(&t);
                else if(snap->oui[0] == oui_rfc1042[0] && snap->oui[1] == oui_rfc1042[1] && // STP
                        snap->oui[2] == oui_rfc1042[2] &&
                        (ntohs(snap->ether_type) >= 0x0000 && ntohs(snap->ether_type) <= 0x05dc) && // len instead ether_type
                        (unsigned)llc2->ssap == 66 && (unsigned)llc2->dsap == 66 && (unsigned)llc2->ctrl1 == 3) { // LLC = STP
                    ofs << "\n\n\n*********************802.11 STP WDS Bridge Frame***********************"
                        << "\n\n802.11 Spanning Tree Protocol WDS Bridge Frame Time Stamp: "   << std::ctime(&t);
                    stpFlag = true;
                }
                else // 1 1 Other WDS
                    ofs << "\n\n\n***********************802.11 WDS Bridge Frame*************************"
                        << "\n\n802.11 WDS Bridge Frame Time Stamp: "   << std::ctime(&t);
            }
            else { // 0 1 or 1 0, non-WDS
                if(snap->oui[0] == oui_cisco2[0] && snap->oui[1] == oui_cisco2[1] && // Cisco Aironet
                   snap->oui[2] == oui_cisco2[2] && ntohs(snap->ether_type) == CISCO_AIRONET_ETHER_TYPE)
                    ofs << "\n\n\n************************802.11 Aironet Frame***************************"
                        << "\n\n802.11 Aironet Frame Time Stamp: "   << std::ctime(&t);
                else { // Unknown Frame
                    ofs << "\n\n\n************************Other Network Frame****************************"
                        << "\n\nOther Network Protocol Frame Time Stamp: " << std::ctime(&t);
                    other = true;
                }
            }

            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            print80211RTAP((cuchar_cptr)rtap, le16toh(rtap->it_len));
            printIEEE80211((cuchar_cptr)ie80211_Buf, ie80211_Size);
            printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
            
            // Check STP WDS
            if(stpFlag)
                printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_ON); // 802.3, eth2 encap

            else
                printSNAP((cuchar_cptr)snap, sizeof(snap_hdr), IEEE80211_SNAP_ETH_802_3_OFF); // eth1 encap

            // Check STP WDS
            if(stpFlag) {
                printLLC((cuchar_cptr)llc2, sizeof(llc_hdr));
                printSTP((cuchar_cptr)stp, sizeof(stphdr));
            }

            // Print Check Frame Sequence
            //ofs << "\nFrame Check Sequence: " << le32toh(fcs->fcs) << '\n';

            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nieee 802.11 Radio Tap Header Dump(pre-pended)";
            header_dump((cuchar_cptr)rtap, le16toh(rtap->it_len));
            ofs << "\nieee 802.11 Header Dump";
            header_dump((cuchar_cptr)ie80211_Buf, ie80211_Size);
            ofs << "\nLogical Link Layer(LLC) Header Dump";
            header_dump((cuchar_cptr)llc, sizeof(llc_hdr));
            ofs << "\nSubnetwork Access Protocol(SNAP) Header Dump";
            header_dump((cuchar_cptr)snap, sizeof(snap_hdr));

            // Check STP WDS
            if(stpFlag) {
                ofs << "\nLogical Link Layer(LLC) Header Dump";
                header_dump((cuchar_cptr)llc2, sizeof(llc_hdr));
                ofs << "\nSpanning Tree Protocol Header Dump";
                header_dump((cuchar_cptr)stp, sizeof(stphdr));
            }
            
            // Prcess Frame Payload
            if(other) {
                ofs << "\nUnknown Payload Dump";
                header_dump((cuchar_cptr)snap + sizeof(snap_hdr), pSize);
            }                
            else if(stpFlag) {
                ofs << "\nPayload Dump";
                header_dump((cuchar_cptr)stp + sizeof(stphdr), stpPSize);
            }
            else { // Other 1 1 WDS, or 1 0 or 0 1 Aironet
                ofs << "\nPayload Dump";
                header_dump((cuchar_cptr)snap + sizeof(snap_hdr), pSize);
            }
            
            // Dump Frame Check Sequence
            //ofs << "\nFrame Check Sequence Dump";
            //header_dump((cuchar_cptr)fcs, sizeof(ieee80211_fcs_hdr));

            ofs << "\n***********************************************************************";

            // Update Totals
            if(other)
                ++otherNetworkC;
            else if(stpFlag)
                ++stpC;
            else // Other 1 1 wds, or 1 0 or 0 1 Aironet
                ++wdsC;
            
            ++totalPC;
            totalBC += len;
            break;
        } // Default End
        } // Ethernet Protocol Switch End
        break;
    }
    case ARPHRD_ETHER: {
        const ethhdr *ethH = (ethhdr*)((cuchar_cptr)packet + packet->tp_mac);

        // Process Ethernet Protocol
        switch(ntohs(sll->sll_protocol)) {
        case ETH_P_IPV6: // IPv6
            // Process IPv6 Below
            /* Fall Trough */
        case ETH_P_IP: { // IPv4
            const iphdr    *ip4H   = (iphdr*)  ((cuchar_cptr)ethH + sizeof(ethhdr));
            const ipv6hdr  *ip6H   = (ipv6hdr*)((cuchar_cptr)ethH + sizeof(ethhdr));
            unsigned short  ip_len = 0;    // opaque buffer size
            unsigned char  *ipH    = NULL; // opaque IP buffer
            unsigned        proto  = 0;    // upper-layer protocol

            // Fill In Correct IP Version, Opaque Buffer, And Size
            if((unsigned)ip4H->version == 4) {
                proto  = (unsigned)ip4H->protocol;
                ip_len = ip4H->ihl * 4; // in bytes
                ipH    = (unsigned char*)((iphdr*)((cuchar_cptr)ethH + sizeof(ethhdr)));
            }
            else {
                proto  = (unsigned)ip6H->nexthdr;
                ip_len = sizeof(ipv6hdr);
                ipH    = (unsigned char*)((ipv6hdr*)((cuchar_cptr)ethH + sizeof(ethhdr)));
            }
            // Process IP Type
            switch(proto) {
            case IPPROTO_ICMP: {
                const icmphdr *icmpH   = (icmphdr*)  ((cuchar_cptr)ipH   + ip_len);
                cuchar_cptr   pBufICM = (cuchar_cptr)((cuchar_cptr)icmpH + sizeof(icmphdr));
                c_uint pSize = len - sizeof(ethhdr) - ip_len - sizeof(icmphdr);

                ofs << "\n\n\n******************************ICMP Packet******************************"
                    << "\n\nICMP Packet Time Stamp: " << std::ctime(&t);

                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);
                printIP((cuchar_cptr)ipH, ip_len);
                printICMP((cuchar_cptr)icmpH, sizeof(icmphdr));

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nEthernet Header Dump";
                header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nICMP Header Dump";
                header_dump((cuchar_cptr)icmpH, sizeof(icmphdr));
                ofs << "\nPayload Dump";
                header_dump(pBufICM, pSize);

                ofs << "\n***********************************************************************";

                // Update Totals
                ++icmpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            case IPPROTO_IGMP: {
                const igmphdr *igmpH   = (igmphdr*)   ((cuchar_cptr)ipH   + ip_len);
                cuchar_cptr    pBufIGM = (cuchar_cptr)((cuchar_cptr)igmpH + sizeof(igmphdr));
                c_uint pSize = len - sizeof(ethhdr) - ip_len - sizeof(igmphdr);

                ofs << "\n\n\n******************************IGMP Packet******************************"
                    << "\n\nIGMP Packet Time Stamp: " << std::ctime(&t);
                
                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);
                printIP((cuchar_cptr)ipH, ip_len);
                printIGMP((cuchar_cptr)igmpH, sizeof(igmphdr));
                
                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nEthernet Header Dump";
                header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nIGMP Header Dump";
                header_dump((cuchar_cptr)igmpH, sizeof(igmphdr));
                ofs << "\nPayload Dump";
                header_dump(pBufIGM, pSize);

                ofs << "\n***********************************************************************";

                // Update Totals
                ++igmpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            case IPPROTO_TCP: {
                const tcphdr         *tcpH    = (tcphdr*)    ((cuchar_cptr)ipH  + ip_len);
                const unsigned short  tcp_len = tcpH->doff * 4; // in bytes
                cuchar_cptr           pBufTCP = (cuchar_cptr)((cuchar_cptr)tcpH + sizeof(tcphdr));
                c_uint pSize = len - sizeof(ethhdr) - ip_len - tcp_len;

                ofs << "\n\n\n******************************TCP  Packet******************************"
                    << "\n\nTCP Packet Time Stamp: "  << std::ctime(&t);

                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);
                printIP((cuchar_cptr)ipH, ip_len);
                printTCP((cuchar_cptr)tcpH, tcp_len);

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nEthernet Header Dump";
                header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nTCP Header Dump";
                header_dump((cuchar_cptr)tcpH, tcp_len);
                ofs << "\nPayload Dump";
                header_dump(pBufTCP, pSize);

                // Readable Dump
                if(readableDumpFlag) {
                    ofs << "\n~~~Decoded Dump~~~"
                        << "\nPayload Decoded Dump";
                    readable_dump(pBufTCP, pSize);
                }

                ofs << "\n***********************************************************************";

                // Parse Payload
                if(parseDumpFlag) {
                    Parser.fill_parser(pBufTCP, len);
                    Parser.parseFile(toParse);
                    Parser.save_parser(pSavePath);
                    Parser.save_parser(pSavePath);
                }

                // Update Totals
                ++tcpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            case IPPROTO_UDP: {
                const udphdr *udpH    = (udphdr*)    ((cuchar_cptr)ipH  + ip_len);
                cuchar_cptr   pBufUDP = (cuchar_cptr)((cuchar_cptr)udpH + sizeof(udphdr));
                c_uint pSize = len - sizeof(ethhdr) - ip_len - sizeof(udphdr);
          
                ofs << "\n\n\n******************************UDP  Packet******************************"
                    << "\n\nUDP Packet Time Stamp: "  << std::ctime(&t);

                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);
                printIP((cuchar_cptr)ipH, ip_len);
                printUDP((cuchar_cptr)udpH, sizeof(udphdr));

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nEthernet Header Dump";
                header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nUDP Header Dump";
                header_dump((cuchar_cptr)udpH, sizeof(udphdr));
                ofs << "\nPayload Dump";
                header_dump(pBufUDP, pSize);

                // Readable Dump
                if(readableDumpFlag) {
                    ofs << "\n~~~Decoded Dump~~~"
                        << "\nPayload Decoded Dump";
                    readable_dump(pBufUDP, pSize);
                }

                ofs << "\n***********************************************************************";

                // Parse Payload
                if(parseDumpFlag) {
                    Parser.fill_parser(pBufUDP, len);
                    Parser.parseFile(toParse);
                    Parser.save_parser(pSavePath);
                    Parser.save_parser(pSavePath);
                }

                // Update Totals
                ++udpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            case IPPROTO_SCTP: {
                const sctphdr2       *sctpH    = (sctphdr2*)      ((cuchar_cptr)ipH    + ip_len);
                const sctp_chunkhdr2 *sctpHC   = (sctp_chunkhdr2*)((cuchar_cptr)sctpH  + sizeof(sctp_chunkhdr2));
                cuchar_cptr           pBufSCTP = (cuchar_cptr)    ((cuchar_cptr)sctpHC + sizeof(sctp_chunkhdr2));
                c_uint pSize = len - sizeof(ethhdr) - ip_len - sizeof(sctphdr2) - sizeof(sctp_chunkhdr2);

                ofs << "\n\n\n******************************SCTP Packet******************************"
                    << "\n\nSCTP Packet Time Stamp: " << std::ctime(&t);

                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);
                printIP((cuchar_cptr)ipH, ip_len);
                printSCTP((cuchar_cptr)sctpH, sizeof(sctphdr2) + sizeof(sctp_chunkhdr2));

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nEthernet Header Dump";
                header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nSCTP Header Dump";
                header_dump((cuchar_cptr)sctpH, sizeof(sctphdr2));
                ofs << "\nSCTP Chunk Header Dump";
                header_dump((cuchar_cptr)sctpHC, sizeof(sctp_chunkhdr2));
                ofs << "\nPayload Dump";
                header_dump(pBufSCTP, pSize);

                ofs << "\n***********************************************************************";

                // Update Totals
                ++sctpC;
                ++totalPC;
                totalBC += len;
                break;
            }
            default: { // Other Transport Packets
                c_uint pSize = len - sizeof(ethhdr) - ip_len;

                ofs << "\n\n\n***********************Other Transport Packet************************"
                    << "\n\nOther IP Protocol Packet Time Stamp: " << std::ctime(&t);
            
                // Print Headers
                printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
                printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
                printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);
                printIP((cuchar_cptr)ipH, ip_len);

                // Dump Data Packets
                ofs << "\n~~~Data Dump~~~";
                ofs << "\nTPacket Header Dump(pre-pended)";
                header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
                ofs << "\nSocket Address Link Layer Header(pre-pended)";
                header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
                ofs << "\nEthernet Header Dump";
                header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
                ofs << "\nIP Header Dump";
                header_dump((cuchar_cptr)ipH, ip_len);
                ofs << "\nUnknown Payload Dump";
                header_dump((cuchar_cptr)ipH + ip_len, pSize); // try to dump

                ofs << "\n***********************************************************************";

                // Update Totals
                ++otherTransportC;
                ++totalPC;
                totalBC += len;
                break;
            } // Default End
            } // Internet Protocol Switch End
            break;
        }
        case ETH_P_PAE: {
            const EAP_hdr *eap = (EAP_hdr*)((cuchar_cptr)ethH + sizeof(ethhdr));
            c_uint pSize = len - sizeof(ethhdr) - sizeof(EAP_hdr);
   
            ofs << "\n\n\n****************************PAE 802.1X Frame****************************"
                << "\n\nPort Access Entity(802.1X) EAP Frame Time Stamp: " << std::ctime(&t);

            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);
            printIEEE8021X((cuchar_cptr)eap, sizeof(EAP_hdr));

            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nEthernet Header Dump";
            header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
            ofs << "\nEAP, PAE 802.1X Header Dump";
            header_dump((cuchar_cptr)eap, sizeof(EAP_hdr));
            ofs << "\nPayload Dump";
            header_dump((cuchar_cptr)eap + sizeof(EAP_hdr), pSize);

            ofs << "\n***********************************************************************";

            // Update Totals
            ++paeC;
            ++totalPC;
            totalBC += len;
            break;
        }
        case ETH_P_ALL:
            // ETH_P_ARP shows up as ETH_P_ALL(0x003) in sll->sll_protocol on some ARP requests
            // ETH II header prints correct value though
            /* Fall Through */
        case ETH_P_ARP: {
            const arphdr2 *arpH = (arphdr2*)((cuchar_cptr)ethH + sizeof(ethhdr));                   
            c_uint pSize = len - sizeof(ethhdr) - sizeof(arphdr2);

            ofs << "\n\n\n******************************ARP   Frame******************************"
                << "\n\nARP Frame Time Stamp: " << std::ctime(&t);

            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);
            printARP((cuchar_cptr)arpH, sizeof(arphdr2));

            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nEthernet Header Dump";
            header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
            ofs << "\nARP Header Dump";
            header_dump((cuchar_cptr)arpH, sizeof(arphdr2));
            ofs << "\nPayload Dump";
            header_dump((cuchar_cptr)arpH + sizeof(arphdr2), pSize);

            ofs << "\n***********************************************************************";

            // Update Totals
            ++arpC;
            ++totalPC;
            totalBC += len;
            break;
        }
        case ETH_P_802_2: { // LLC, non DIX type (usually only used for wifi and 802.3, not ETH II)
            const llc_hdr *llc = (llc_hdr*)((cuchar_cptr)ethH + sizeof(ethhdr));
            const stphdr  *stp = (stphdr*) ((cuchar_cptr)llc  + sizeof(llc_hdr));
            c_uint pSizeSTP = len - sizeof(ethhdr) - sizeof(stphdr);
            c_uint pSizeLLC = len - sizeof(ethhdr) - sizeof(llc_hdr);

            // Process LSAP
            if((unsigned)llc->dsap == 66) // STP = 66
                ofs << "\n\n\n***************************STP 802.1d Frame****************************"
                    << "\n\nSpanning Tree Protocol Frame, 802.1d Time Stamp: " << std::ctime(&t);
            else
                ofs << "\n\n\n****************************LLC 802.2 Frame****************************"
                    << "\n\nLLC 802.2 Frame Time Stamp: " << std::ctime(&t);
            
            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), true);
            printLLC((cuchar_cptr)llc, sizeof(llc_hdr));
            
            // Process LSAP
            if((unsigned)llc->dsap == 66)
                printSTP((cuchar_cptr)stp, sizeof(stphdr));

            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nEthernet Header Dump";
            header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
            ofs << "\nLogical Link Layer(LLC) Header Dump";
            header_dump((cuchar_cptr)llc, sizeof(llc_hdr));

            // Process LSAP
            if((unsigned)llc->dsap == 66) {
                ofs << "\nSpanning Tree Protocol Header Dump";
                header_dump((cuchar_cptr)stp, sizeof(stphdr));
                ofs << "\nPayload Dump";
                header_dump((cuchar_cptr)stp + sizeof(stphdr), pSizeSTP);
            }
            else {
                ofs << "\nPayload Dump";
                header_dump((cuchar_cptr)llc + sizeof(llc_hdr), pSizeLLC);
            }

            ofs << "\n***********************************************************************";

            // Update Totals
            if((unsigned)llc->dsap == 66)
                ++stpC;
            else
                ++otherNetworkC;
            
            ++totalPC;
            totalBC += len;
            break;
        }
        case ETH_P_PPP_MP: {
            c_uint pSize = len - sizeof(ethhdr);

            ofs << "\n\n\n*****************************PPP MP Frame******************************"
                << "\n\nPoint-To-Point Protocol Multilink Frame Time Stamp: " << std::ctime(&t);

            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);
            
            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nEthernet Header Dump";
            header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
            ofs << "\nPayload Dump";
            header_dump((cuchar_cptr)ethH + sizeof(ethhdr), pSize);

            ofs << "\n***********************************************************************";
            
            // Update Totals
            ++otherNetworkC;
            ++totalPC;
            totalBC += len;
            break;
        }
        default: { // Other Ether_Types
            c_uint pSize = len - sizeof(ethhdr);

            ofs << "\n\n\n*************************Other Network Frame***************************"
                << "\n\nOther Network Protocol Frame Time Stamp: " << std::ctime(&t);

            // Print Headers
            printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));
            printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));
            printEthernet((cuchar_cptr)ethH, sizeof(ethhdr), false);

            // Dump Data Packets
            ofs << "\n~~~Data Dump~~~";
            ofs << "\nTPacket Header Dump(pre-pended)";
            header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
            ofs << "\nSocket Address Link Layer Header(pre-pended)";
            header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
            ofs << "\nEthernet Header Dump";
            header_dump((cuchar_cptr)ethH, sizeof(ethhdr));
            ofs << "\nUnknown Transport + Payload Dump"; 
            header_dump((cuchar_cptr)ethH + sizeof(ethhdr), pSize); // try to dump
         
            ofs << "\n***********************************************************************";

            // Update Totals
            ++otherNetworkC;
            ++totalPC;
            totalBC += len;
            break;
        } // Default End
        } // Ethernet Protocol Switch End
        break;
    }
    default: { // Other Data-Link Frames
        ofs << "\n\n\n*************************Other Data-Link Frame*************************"
            << "\n\nOther Hardware Type Frame Time Stamp: " << std::ctime(&t);

        // Print Headers
        printTPACKET((cuchar_cptr)packet, TPACKET2_HDRLEN - sizeof(sockaddr_ll));  
        printSADDR_LL((cuchar_cptr)sll, sizeof(sockaddr_ll));  

        // Dump Data Packets
        ofs << "\n~~~Data Dump~~~";
        ofs << "\nTPacket Header Dump(pre-pended)";
        header_dump((cuchar_cptr)packet, sizeof(tpacket2_hdr));
        ofs << "\nSocket Address Link Layer Header(pre-pended)";
        header_dump((cuchar_cptr)sll, sizeof(sockaddr_ll));
        ofs << "\nUnknown Data-Link + Payload Dump";
        header_dump((cuchar_cptr)packet + packet->tp_mac, len); // try to dump

        ofs << "\n***********************************************************************";

        // Update Totals
        ++otherDataLinkC;
        ++totalPC;
        totalBC += len;
        break;
    } // Default End
    } // Hardware Type Switch End

    // Flush
    ofs.flush();
    std::fflush(stdout);
}

void Sniffer::printTPACKET(cuchar_cptr packet, c_uint len) { // pre-pended
    // Declarations
    const tpacket2_hdr *tpack = (tpacket2_hdr*)packet;

    // Defines
    #define TSTAT tpack->tp_status

    // Print TPacket Header
    ofs << "\n~~~TPacket Header(pre-pended)~~~"
        << "\nStatus Sum:           " << TSTAT
        << "\nOwner:                "
        << (!(TSTAT & ~TP_STATUS_KERNEL)         ? "Kernel"
          :   TSTAT &  TP_STATUS_USER            ? "User"
          :                                        "Unknown") // shouldn't happen
        << "\nCopy:                 "
        << (  TSTAT &  TP_STATUS_COPY            ? '1' : '0')
        << "\nLosing:               "
        << (  TSTAT &  TP_STATUS_LOSING          ? '1' : '0')
        << "\nCheck Some Not Ready: "
        << (  TSTAT &  TP_STATUS_CSUMNOTREADY    ? '1' : '0')
        << "\nValid VLAN TCI:       "
        << (  TSTAT &  TP_STATUS_VLAN_VALID      ? '1' : '0')
        << "\nBlock Timeout:        "
        << (  TSTAT &  TP_STATUS_BLK_TMO         ? '1' : '0')
        << "\nValid VLAN TPID:      "
        << (  TSTAT &  TP_STATUS_VLAN_TPID_VALID ? '1' : '0')
        << "\nLength:               " << tpack->tp_len
        << "\nSnap Len:             " << tpack->tp_snaplen
        << "\nMAC Offset:           " << tpack->tp_mac
        << "\nNET Offset:           " << tpack->tp_net
        << "\nSeconds:              " << tpack->tp_sec
        << "\nNano Seconds:         " << tpack->tp_nsec
        << "\nVLAN TCI:             " << tpack->tp_vlan_tci
      //<< "\nVLAN TPID:            " << tpack->tp_vlan_tpid
        << '\n';
    ofs.flush();

    // Undefines
    #undef TSTAT
}

void Sniffer::printSADDR_LL(cuchar_cptr packet, c_uint len) {  // pre-pended
    // Declarations
    const sockaddr_ll *sll = (sockaddr_ll*)packet;
    unsigned char addr[HARDWARE_PRINT_LEN];

    // Zero Out
    std::memset(addr, 0, HARDWARE_PRINT_LEN);   

    // Defines
    #define SFAM sll->sll_family
    #define SPKT (unsigned)sll->sll_pkttype

    // Format MAC Address
    if((unsigned)sll->sll_halen == ETH_ALEN)
        std::snprintf((char*)addr, HARDWARE_PRINT_LEN, "%.2X:%.2X:%.2X:%.2X:%.2X:%.2X",
            sll->sll_addr[0], sll->sll_addr[1], sll->sll_addr[2],
            sll->sll_addr[3], sll->sll_addr[4], sll->sll_addr[5]);
    else // other hardware type length
        std::snprintf((char*)addr, HARDWARE_PRINT_LEN, "%.2X:%.2X:%.2X:%.2X:%.2X:%.2X:%.2X:%.2X",
            sll->sll_addr[0], sll->sll_addr[1], sll->sll_addr[2],
            sll->sll_addr[3], sll->sll_addr[4], sll->sll_addr[5],
            sll->sll_addr[6], sll->sll_addr[7]);

    // Print Socket Address Link Layer Header
    ofs << "\n~~~Socket Address Link Layer Header(pre-pended)~~~"
        << "\nFamily:            " << SFAM << ": AF_PACKET"
        << "\nProtocol:          " << ntohs(sll->sll_protocol);
    printEtherType(ntohs(sll->sll_protocol));
    ofs << "\nIf Index:          " << sll->sll_ifindex
        << "\nHardware Type:     " << sll->sll_hatype;
    printARP_HAType(sll->sll_hatype);
    ofs << "\nPacket Type:       " << SPKT
        << (SPKT == PACKET_HOST      ? ": Packet Host(to us)"
          : SPKT == PACKET_BROADCAST ? ": Packet Broadcast(to all)"
          : SPKT == PACKET_MULTICAST ? ": Packet Multicast(to group)"
          : SPKT == PACKET_OTHERHOST ? ": Packet Otherhost(to someone else)"
          : SPKT == PACKET_OUTGOING  ? ": Packet Outgoing(to any type)"
          : SPKT == PACKET_LOOPBACK  ? ": Packet Loopback(MC/BRD frame)"      // invisible from userland
          : SPKT == PACKET_FASTROUTE ? ": Packet Fastroute(Fastrouted frame)" // invisible from userland
          :                            ": Packet Unknown")
        << "\nHardware Addr Len: " << (unsigned)sll->sll_halen
        << "\nHardware Address:  " << addr
        << '\n';
    ofs.flush();

    // Undefines
    #undef SFAM
    #undef SPKT
}

void Sniffer::print80211RTAP(cuchar_cptr packet, c_uint len) { // pre-pended
    // Declarations
    ie80211_rtaphdr_rx *rtap = (ie80211_rtaphdr_rx*)packet;

    // Defines
    #define RT_FLAGS   (unsigned)rtap->rt_flags
    #define CHAN_FLAGS le16toh(rtap->rt_chan_flags)
    
    // Print Radio Tap Header
    ofs << "\n~~~ieee 802.11 Radio Tap Header(pre-pended)~~~"
        << "\nVersion:             " << (unsigned)rtap->it_version // linux only supports version 0
        << "\nLength:              " << le16toh(rtap->it_len)
        << "\nPresent Total:       " << le32toh(rtap->it_present)
        << "\nTSFT(mactime):       " << (_GET_TSFT(&rtap->it_present)         ? '1' : '0')
        << "\nFlags:               " << (_GET_FLAGS(&rtap->it_present)        ? '1' : '0')
        << "\nRate:                " << (_GET_RATE(&rtap->it_present)         ? '1' : '0')
        << "\nChannel + Flags:     " << (_GET_CHANNEL(&rtap->it_present)      ? '1' : '0')
        << "\nFHSS:                " << (_GET_FHSS(&rtap->it_present)         ? '1' : '0')
        << "\nDBM Antenna Signal:  " << (_GET_ANTSIGNAL(&rtap->it_present)    ? '1' : '0')
        << "\nDBM Antenna Noise:   " << (_GET_ANTNOISE(&rtap->it_present)     ? '1' : '0')
        << "\nLock Quality:        " << (_GET_LOCKQUALITY(&rtap->it_present)  ? '1' : '0')
        << "\nDBM TX Attenuation:  " << (_GET_TX_ATTEN(&rtap->it_present)     ? '1' : '0')
        << "\nDB TX Attenuation:   " << (_GET_DB_TX_ATTEN(&rtap->it_present)  ? '1' : '0')
        << "\nDBM TX Power:        " << (_GET_DBM_TXPWR(&rtap->it_present)    ? '1' : '0')
        << "\nAntenna Index:       " << (_GET_ANTENNA(&rtap->it_present)      ? '1' : '0')
        << "\nDB Antenna Signal:   " << (_GET_DB_ANTSIG(&rtap->it_present)    ? '1' : '0')
        << "\nDB Antenna Noise:    " << (_GET_DB_ANTNOISE(&rtap->it_present)  ? '1' : '0')
        << "\nRX Flags:            " << (_GET_RX_FLAGS(&rtap->it_present)     ? '1' : '0')
        << "\nTX Flags:            " << (_GET_TX_FLAGS(&rtap->it_present)     ? '1' : '0')
        << "\nRTS Retries:         " << (_GET_RTS_RETRIES(&rtap->it_present)  ? '1' : '0')
        << "\nData Retries:        " << (_GET_DATA_RETRIES(&rtap->it_present) ? '1' : '0')
        << "\nMCS:                 " << (_GET_MCS(&rtap->it_present)          ? '1' : '0')
        << "\nA-MPDU Stats:        " << (_GET_AMPDU_STATS(&rtap->it_present)  ? '1' : '0')
        << "\nVHT:                 " << (_GET_VHT(&rtap->it_present)          ? '1' : '0')
        << "\nRadiotap Namespace:  " << (_GET_RTAP_NSPACE(&rtap->it_present)  ? '1' : '0')
        << "\nVendor Namespace:    " << (_GET_VEND_NSPACE(&rtap->it_present)  ? '1' : '0')
        << "\nBitmap Extension:    " << (_GET_BITMAP_EXT(&rtap->it_present)   ? '1' : '0');

    // Parse Present Bitma
    ofs << "\n\n~Present Information~";
    if(_GET_TSFT(&rtap->it_present))
        ofs << "\nTSFT(mactime):       " << le64toh(rtap->rt_tsft);
    if(_GET_FLAGS(&rtap->it_present)) {
        ofs << "\nFlags Total:         " << RT_FLAGS;
    
        // Check Flags Bitmask
        if(RT_FLAGS & 0x01)
            ofs << "\n                     Sent/Received During CFP";
        if(RT_FLAGS & 0x02)
            ofs << "\n                     Sent/Received With Short Preamable";
        if(RT_FLAGS & 0x04)
            ofs << "\n                     Sent/Received With WEP Encryption";
        if(RT_FLAGS & 0x08)
            ofs << "\n                     Sent/Received With Fragmentation";
        if(RT_FLAGS & 0x10)
            ofs << "\n                     Frame Includes FCS";
        if(RT_FLAGS & 0x20)
            ofs << "\n                     Frame Pad Between 802.11 Header And Payload(32-bit Bound)";
        if(RT_FLAGS & 0x40)
            ofs << "\n                     Frame Failed FCS CRC";
        if(RT_FLAGS & 0x80)
            ofs << "\n                     Frame Used Short Guard Interval(HT)";
    }
    if(_GET_RATE(&rtap->it_present))
        ofs << "\nRX Rate:             "
            << ((float)(unsigned)rtap->rt_rate * 500.00) / 1000.00 << " Mb/s"; // 500 Kbps units
    if(_GET_CHANNEL(&rtap->it_present)) {
        ofs << "\nChannel:             ";
        
        // Check GHz/MHz
        if((float)le16toh(rtap->rt_chan) >= 1000.00) {
            ofs << std::showpoint << std::fixed << std::setprecision(3)
                << (float)le16toh(rtap->rt_chan) / 1000.00 << " GHz";
            ofs.unsetf(std::ios::showpoint); // unset
            ofs.unsetf(std::ios::fixed);     // unset
        }
        else
            ofs << le16toh(rtap->rt_chan) << " MHz";

        ofs << "\nChannel Flags Total: " << le16toh(rtap->rt_chan_flags);
        
        // Check Flags Bitmask
        if(CHAN_FLAGS & 0x0010)
            ofs << "\n                     Turbo Channel";
        if(CHAN_FLAGS & 0x0020)
            ofs << "\n                     CCK Channel";
        if(CHAN_FLAGS & 0x0040)
            ofs << "\n                     OFDM Channel";
        if(CHAN_FLAGS & 0x0080)
            ofs << "\n                     2 GHz Spectrum Channel";
        if(CHAN_FLAGS & 0x0100)
            ofs << "\n                     5 GHz Spectrum Channel";
        if(CHAN_FLAGS & 0x0200)
            ofs << "\n                     Only Passive Scan Allowed";
        if(CHAN_FLAGS & 0x0400)
            ofs << "\n                     Dynamic CCK-OFDM Channel";
        if(CHAN_FLAGS & 0x0800)
            ofs << "\n                     GFSK Channel(FHSS PHY)";
        if(CHAN_FLAGS & 0x1000)
            ofs << "\n                     GSM(900 MHz)";
        if(CHAN_FLAGS & 0x2000)
            ofs << "\n                     Static Turbo";
        if(CHAN_FLAGS & 0x4000)
            ofs << "\n                     Half Channel(10 MHz Wide)";
        if(CHAN_FLAGS & 0x8000)
            ofs << "\n                     Quarter Channel(5 Mhz Wide)";
    }
    if(_GET_FHSS(&rtap->it_present))
        ofs << "\nFHSS:                ";
    if(_GET_ANTSIGNAL(&rtap->it_present))
        ofs << "\nAntenna Signal:      " << (signed)rtap->rt_antsignal << " dBm";
    if(_GET_ANTNOISE(&rtap->it_present))
        ofs << "\nAntenna Noise:       " << (signed)rtap->rt_antnoise  << " dBm";
    if(_GET_LOCKQUALITY(&rtap->it_present))
        ofs << "\nLock Quality:        ";
    if(_GET_TX_ATTEN(&rtap->it_present))
        ofs << "\nTX Attenuation:      ";
    if(_GET_DB_TX_ATTEN(&rtap->it_present))
        ofs << "\nDB TX Attenuation:   ";
    if(_GET_DBM_TXPWR(&rtap->it_present))
        ofs << "\nTX Power:            ";
    if(_GET_ANTENNA(&rtap->it_present))
        ofs << "\nAntenna Index:       " << (unsigned)rtap->rt_antenna;
    if(_GET_DB_ANTSIG(&rtap->it_present))
        ofs << "\nDB Antenna Signal:   ";
    if(_GET_DB_ANTNOISE(&rtap->it_present))
        ofs << "\nDB Antenna Noise:    ";
    if(_GET_RX_FLAGS(&rtap->it_present)) {
        //ofs << "\nRX Flags Total:      " << le16toh(rtap->rt_rx_flags);

        // Check Flags Bitmask
        //if(le16toh(rtap->rt_rx_flags) & 0x0001)
        //    ofs << "\n                     Reserved (Was FCS Failed But Is Regular Flag)";
        //if(le16toh(rtap->rt_rx_flags) & 0x0002)
        //    ofs << "\n                     PLCP CRC Check Failed";
        //if(le16toh(rtap->rt_rx_flags) & 0xfffc)
        //    ofs << "\n                     Reserved, Future Expansion";
    }
    if(_GET_TX_FLAGS(&rtap->it_present))
        ofs << "\nTX Flags Total:      ";
    if(_GET_RTS_RETRIES(&rtap->it_present))
        ofs << "\nRTS Retries:         ";
    if(_GET_DATA_RETRIES(&rtap->it_present))
        ofs << "\nData Retries:        ";
    if(_GET_MCS(&rtap->it_present))
        ofs << "\nMCS:                 ";
    if(_GET_AMPDU_STATS(&rtap->it_present))
        ofs << "\nA-MPDU Stats:        ";
    if(_GET_VHT(&rtap->it_present))
        ofs << "\nVHT:                 ";
    if(_GET_RTAP_NSPACE(&rtap->it_present))
        ofs << "\nRadiotap Namespace:  ";
    if(_GET_VEND_NSPACE(&rtap->it_present))
        ofs << "\nVendor Namespace:    ";
    if(_GET_BITMAP_EXT(&rtap->it_present))
        ofs << "\nBitmap Extension:    ";

    ofs << '\n';
    ofs.flush();

    // Undefines
    #undef RT_FLAGS
    #undef CHAN_FLAGS
}

void Sniffer::print80211Status(const __le16 status) {
    // Print IEEE 802.11 Management Frame Status Code
    switch(le16toh(status)) {
    case WLAN_STATUS_SUCCESS:
        ofs << ": Success";
        break;
    case WLAN_STATUS_UNSPECIFIED_FAILURE:
        ofs << ": Unspecified Failure";
        break;
    case WLAN_STATUS_CAPS_UNSUPPORTED:
        ofs << ": Capabilities Unsupported";
        break;
    case WLAN_STATUS_REASSOC_NO_ASSOC:
        ofs << ": Reassociation, No Association";
        break;
    case WLAN_STATUS_ASSOC_DENIED_UNSPEC:
        ofs << ": Association Denied, Unspecified"; 
        break;
    case WLAN_STATUS_NOT_SUPPORTED_AUTH_ALG:
        ofs << ": Not Supported, Authentication Algorithm";
        break;
    case WLAN_STATUS_UNKNOWN_AUTH_TRANSACTION:
        ofs << ": Unknown Authentication Transaction";
        break;
    case WLAN_STATUS_CHALLENGE_FAIL:
        ofs << ": Challenge Failure";
        break;
    case WLAN_STATUS_AUTH_TIMEOUT:
        ofs << ": Authentication Timeout";
        break;
    case WLAN_STATUS_AP_UNABLE_TO_HANDLE_NEW_STA:
        ofs << ": AP Unable To Handle New Station";
        break;
    case WLAN_STATUS_ASSOC_DENIED_RATES:
        ofs << ": Association Denied, Rates";
        break;
    // 802.11b
    case WLAN_STATUS_ASSOC_DENIED_NOSHORTPREAMBLE:
        ofs << ": Association Denied, No Short Preamble";
        break;
    case WLAN_STATUS_ASSOC_DENIED_NOPBCC:
        ofs << ": Association Denied, No PBCC";
        break;
    case WLAN_STATUS_ASSOC_DENIED_NOAGILITY:
        ofs << ": Association Denied, No Agility";
        break;
    // 802.11h
    case WLAN_STATUS_ASSOC_DENIED_NOSPECTRUM:
        ofs << ": Association Denied, No Spectrum";
        break;
    case WLAN_STATUS_ASSOC_REJECTED_BAD_POWER:
        ofs << ": Association Rejected, Bad Power";
        break;
    case WLAN_STATUS_ASSOC_REJECTED_BAD_SUPP_CHAN:
        ofs << ": Association Rejected, Bad Suppprted Channel";
        break;
    // 802.11g
    case WLAN_STATUS_ASSOC_DENIED_NOSHORTTIME:
        ofs << ": Association Denied, No Short Time"; 
        break;
    case WLAN_STATUS_ASSOC_DENIED_NODSSSOFDM:
        ofs << ": Association Denied, No DSSSOFDM";
        break;
    // 802.11w
    case WLAN_STATUS_ASSOC_REJECTED_TEMPORARILY:
        ofs << ": Association Rejected, Temporarily";
        break;
    case WLAN_STATUS_ROBUST_MGMT_FRAME_POLICY_VIOLATION:
        ofs << ": Robust MGMT Frame Policy Violation";
        break;
    // 802.11i
    case WLAN_STATUS_INVALID_IE:
        ofs << ": Invalid Information Element";
        break;
    case WLAN_STATUS_INVALID_GROUP_CIPHER:
        ofs << ": Invalid Group Cipher";
        break;
    case WLAN_STATUS_INVALID_PAIRWISE_CIPHER:
        ofs << ": Invalid Pairwise Cipher";
        break;
    case WLAN_STATUS_INVALID_AKMP:
        ofs << ": Invalid AKMP";
        break;
    case WLAN_STATUS_UNSUPP_RSN_VERSION:
        ofs << ": Unsupported RSN Version";
        break;
    case WLAN_STATUS_INVALID_RSN_IE_CAP:
        ofs << ": Invalid RSN IE Capability";
        break;
    case WLAN_STATUS_CIPHER_SUITE_REJECTED:
        ofs << ": Cipher Suite Rejected";
        break;
    // 802.11e
    case WLAN_STATUS_UNSPECIFIED_QOS:
        ofs << ": Unspecified QOS";
        break;
    case WLAN_STATUS_ASSOC_DENIED_NOBANDWIDTH:
        ofs << ": Association Denied, No Bandwidth";
        break;
    case WLAN_STATUS_ASSOC_DENIED_LOWACK:
        ofs << ": Association Denied, Low Acknowledgment";
        break;
    case WLAN_STATUS_ASSOC_DENIED_UNSUPP_QOS:
        ofs << ": Association Denied, Unsupported QOS";
        break;
    case WLAN_STATUS_REQUEST_DECLINED:
        ofs << ": Request Declined";
        break;
    case WLAN_STATUS_INVALID_QOS_PARAM:
        ofs << ": Invalid QOS Parameter";
        break;
    case WLAN_STATUS_CHANGE_TSPEC:
        ofs << ": Change Time Specification";
        break;
    case WLAN_STATUS_WAIT_TS_DELAY:
        ofs << ": Wait, TS Delay";
        break;
    case WLAN_STATUS_NO_DIRECT_LINK:
        ofs << ": No Direct Link";
        break;
    case WLAN_STATUS_STA_NOT_PRESENT:
        ofs << ": Station Not Present";
        break;
    case WLAN_STATUS_STA_NOT_QSTA:
        ofs << ": Station Not QSTA";
        break;
    // 802.11s
    case WLAN_STATUS_ANTI_CLOG_REQUIRED:
        ofs << ": Anti-Clog Required";
        break;
    case WLAN_STATUS_FCG_NOT_SUPP:
        ofs << ": FCG Not Suppprted";
        break;
//  case WLAN_STATUS_STA_NO_TBTT:
//      break;
    // 802.11ad
//  case WLAN_STATUS_REJECTED_WITH_SUGGESTED_CHANGES:///////////////////////////////////////
//      break;
//  case WLAN_STATUS_REJECTED_FOR_DELAY_PERIOD:
//      break;
    case WLAN_STATUS_REJECT_WITH_SCHEDULE:
        ofs << ": Rejected With Schedule";
        break;
    case WLAN_STATUS_PENDING_ADMITTING_FST_SESSION:
        ofs << ": Pending Admitting FST Session";
        break;
    case WLAN_STATUS_PERFORMING_FST_NOW:
        ofs << ": Performing FST Now";
        break;
    case WLAN_STATUS_PENDING_GAP_IN_BA_WINDOW:
        ofs << ": Pending Gap In BA Window";
        break;
    case WLAN_STATUS_REJECT_U_PID_SETTING:
        ofs << ": Rejected U PID Setting";
        break;
    case WLAN_STATUS_REJECT_DSE_BAND:
        ofs << ": Rejected DSE Band";
        break;
    case WLAN_STATUS_DENIED_WITH_SUGGESTED_BAND_AND_CHANNEL:
        ofs << ": Denied With Suggested Band And Channel";
        break;
    case WLAN_STATUS_DENIED_DUE_TO_SPECTRUM_MANAGEMENT:
        ofs << ": Denied Due To Spectrum Management";
        break;
    default: // check online
        ofs << ": Unknown Status Code";
        break;
    };
}

void Sniffer::print80211Reason(const __le16 reason) {
    // Print IEEE 802.11 Management Frame Reaon Code
    switch(le16toh(reason)) {
    case WLAN_REASON_UNSPECIFIED:
        ofs << ": Unspecified";
        break;
    case WLAN_REASON_PREV_AUTH_NOT_VALID:
        ofs << ": Previous Authentication Not Valid";
        break;
    case WLAN_REASON_DEAUTH_LEAVING:
        ofs << ": Deauthentication, Leaving";
        break;
    case WLAN_REASON_DISASSOC_DUE_TO_INACTIVITY:
        ofs << ": Disassociation Due To Inactivity";
        break;
    case WLAN_REASON_DISASSOC_AP_BUSY:
        ofs << ": Disassociation, AP Busy"; 
        break;
    case WLAN_REASON_CLASS2_FRAME_FROM_NONAUTH_STA:
        ofs << ": Class 2 Frame From Non-Auth Station";
        break;
    case WLAN_REASON_CLASS3_FRAME_FROM_NONASSOC_STA:
        ofs << ": Class 3 Frame From Non-Assoc Station";
        break;
    case WLAN_REASON_DISASSOC_STA_HAS_LEFT:
        ofs << ": Disassociation, Station Has Left";
        break;
    case WLAN_REASON_STA_REQ_ASSOC_WITHOUT_AUTH:
        ofs << ": Station Request Association Without Auth";
    break;
    // 802.11h
    case WLAN_REASON_DISASSOC_BAD_POWER:
        ofs << ": Disassociation, Bad Power";
        break;
    case WLAN_REASON_DISASSOC_BAD_SUPP_CHAN:
        ofs << ": Disassociation, Bad Supported Channel";
        break;
    // 802.11i
    case WLAN_REASON_INVALID_IE:
        ofs << ": Invalid Information Element";
        break;
    case WLAN_REASON_MIC_FAILURE:
        ofs << ": MIC Failure";
        break;
    case WLAN_REASON_4WAY_HANDSHAKE_TIMEOUT:
        ofs << ": 4-Way Handshake Timeout";
        break;
    case WLAN_REASON_GROUP_KEY_HANDSHAKE_TIMEOUT:
        ofs << ": Group Key Handshake Timeout";
        break;
    case WLAN_REASON_IE_DIFFERENT:
        ofs << ": Information Element Different";
        break;
    case WLAN_REASON_INVALID_GROUP_CIPHER:
        ofs << ": Invalid Group Cipher";
        break;
    case WLAN_REASON_INVALID_PAIRWISE_CIPHER:
        ofs << ": Invalid Pairwise Cipher"; 
        break;
    case WLAN_REASON_INVALID_AKMP:
        ofs << ": Invalid AKMP";
        break;
    case WLAN_REASON_UNSUPP_RSN_VERSION:
        ofs << ": Unsupported Reason Version";
        break;
    case WLAN_REASON_IEEE8021X_FAILED:
        ofs << ": IEEE 802.1x Failed";
        break;
    case WLAN_REASON_CIPHER_SUITE_REJECTED:
        ofs << ": Cipher Suite Rejected";
        break;
    // 802.11z TDLS
    case WLAN_REASON_TDLS_TEARDOWN_UNREACHABLE:
        ofs << ": TDLS, Teardown Unreachable";
        break;
    case WLAN_REASON_TDLS_TEARDOWN_UNSPECIFIED:
        ofs << ": TDLS, Teardown Unspecified";
        break;
    // 802.11e
    case WLAN_REASON_DISASSOC_UNSPECIFIED_QOS:
        ofs << ": Disassociation, Unspecified QOS";
        break;
    case WLAN_REASON_DISASSOC_QAP_NO_BANDWIDTH:
        ofs << ": Disassociation, QAP No Bandwidth";
        break;
    case WLAN_REASON_DISASSOC_LOW_ACK:
        ofs << ":Disassociation, Low Acknowledgment";
        break;
    case WLAN_REASON_DISASSOC_QAP_EXCEED_TXOP:
        ofs << ": Disassociation, QAP Exceeded TXOP";
        break;
    case WLAN_REASON_QSTA_LEAVE_QBSS:
        ofs << ": QSTA, Leave QBSS";
        break;
    case WLAN_REASON_QSTA_NOT_USE:
        ofs << ": QSTA, Not Used";
        break;
    case WLAN_REASON_QSTA_REQUIRE_SETUP:
        ofs << ": QSTA, Requires Setup";
        break;
    case WLAN_REASON_QSTA_TIMEOUT:
        ofs << ": QSTA, Timeout";
        break;
    case WLAN_REASON_QSTA_CIPHER_NOT_SUPP:
        ofs << ": QSTA, Cipher Not Supported";
        break;
    // 802.11s
    case WLAN_REASON_MESH_PEER_CANCELED:
        ofs << ": MESH, Peer Canceled";
        break;
    case WLAN_REASON_MESH_MAX_PEERS:
        ofs << ": MESH, Max Peers";
        break;
    case WLAN_REASON_MESH_CONFIG:
        ofs << ": MESH, Configuration";
        break;
    case WLAN_REASON_MESH_CLOSE:
        ofs << ": MESH, Close";
        break;
    case WLAN_REASON_MESH_MAX_RETRIES:
        ofs << ": MESH, Max Retries";
        break;
    case WLAN_REASON_MESH_CONFIRM_TIMEOUT:
        ofs << ": MESH, Confirm Timeout";
        break;
    case WLAN_REASON_MESH_INVALID_GTK:
        ofs << ": MESH, Invalid GTK";
        break;
    case WLAN_REASON_MESH_INCONSISTENT_PARAM:
        ofs << ": MESH, Inconsistent Parameter";
        break;
    case WLAN_REASON_MESH_INVALID_SECURITY:
        ofs << ": MESH, Invalid Security";
        break;
    case WLAN_REASON_MESH_PATH_ERROR:
        ofs << ": MESH, Path Error";
        break;
    case WLAN_REASON_MESH_PATH_NOFORWARD:
        ofs << ": MESH, Path No Forwarding";
        break;
    case WLAN_REASON_MESH_PATH_DEST_UNREACHABLE:
        ofs << ": MESH, Path Destination Unreachable";
        break;
    case WLAN_REASON_MAC_EXISTS_IN_MBSS:
        ofs << ": MAC Exists In MBSS";
        break;
    case WLAN_REASON_MESH_CHAN_REGULATORY:
        ofs << ": MESH< Channel Regulatory";
        break;
    case WLAN_REASON_MESH_CHAN:
        ofs << ": MESH, Channel";
        break;
    default: // check online
        ofs << ": Unknown Reason Code";
        break;
    };
}

void Sniffer::print80211ActionCat(const unsigned char category) {
    switch(category) {
    case WLAN_CATEGORY_SPECTRUM_MGMT:
        ofs << ": Spectrum Management";
        break;
    case WLAN_CATEGORY_QOS:
        ofs << ": QOS";           
        break;
    case WLAN_CATEGORY_DLS:
        ofs << ": Direct Link Setup";
        break;
    case WLAN_CATEGORY_BACK:
        ofs << ": Blocked Acknowledgment(BACK)";
        break;
    case WLAN_CATEGORY_PUBLIC:
        ofs << ": Public";
        break;
    case WLAN_CATEGORY_RADIO_MEASUREMENT:
        ofs << ": Radio Measurement";
        break;
    case WLAN_CATEGORY_HT: // 802.11n
        ofs << ": High Throughput(HT)";
        break;       
    case WLAN_CATEGORY_SA_QUERY:
        ofs << ": SA Query";
        break;
    case WLAN_CATEGORY_PROTECTED_DUAL_OF_ACTION:
        ofs << ": Protected Dual Of Acion";
        break;
    case WLAN_CATEGORY_TDLS:
        ofs << ": TDLS"; // 802.11z
        break;
    case WLAN_CATEGORY_MESH_ACTION:
        ofs << ": MESH Action"; // 802.11s
        break;
    case WLAN_CATEGORY_MULTIHOP_ACTION:
        ofs << ": Multi-Hop Action";
        break;
    case WLAN_CATEGORY_SELF_PROTECTED:
        ofs << ": Self Protected";
        break;
    case WLAN_CATEGORY_DMG:
        ofs << ": DMG";
        break;
    case WLAN_CATEGORY_WMM:
        ofs << ": WMM";
        break;
    case WLAN_CATEGORY_FST:
        ofs << ": FST";
        break;
    case WLAN_CATEGORY_UNPROT_DMG:
        ofs << ": Unprotected DMG";
        break;
    case WLAN_CATEGORY_VHT:
        ofs << ": Very High Throughput(VHT)"; // 802.11ac
        break;
    case WLAN_CATEGORY_VENDOR_SPECIFIC_PROTECTED:
        ofs << ": Vendor Specific Protected";
        break;
    case WLAN_CATEGORY_VENDOR_SPECIFIC:
        ofs << ": Vendor Specific";
        break;
    default:
        ofs << ": Unknown Action Category";
        break;
    };
}

void Sniffer::printIEEE80211(cuchar_cptr packet, c_uint len) {
    // Declarations
    const u_ieee80211_hdrs *ie80211_un = (u_ieee80211_hdrs*)packet; // union of all
    const ieee80211_ie     *ie80211_IE = (ieee80211_ie*)(ie80211_un + len);
    std::string   saddr1, saddr2, saddr3, saddr4, flow;
    unsigned char addr1[ETH_PRINT_LEN], addr2[ETH_PRINT_LEN],
                  addr3[ETH_PRINT_LEN], addr4[ETH_PRINT_LEN];
    unsigned char da[ETH_PRINT_LEN], sa[ETH_PRINT_LEN],
                  ta[ETH_PRINT_LEN], ra[ETH_PRINT_LEN],
                  bssid[ETH_PRINT_LEN],
                  cur_ap[ETH_PRINT_LEN],
                  trans_id[WLAN_SA_QUERY_TR_ID_LEN];
    bool          addr_count_is_3 = false, qos = false;

    // Zero Out
    std::memset(da,       0, ETH_PRINT_LEN);
    std::memset(sa,       0, ETH_PRINT_LEN);
    std::memset(ta,       0, ETH_PRINT_LEN);
    std::memset(ra,       0, ETH_PRINT_LEN);
    std::memset(bssid,    0, ETH_PRINT_LEN);   
    std::memset(cur_ap,   0, ETH_PRINT_LEN);
    std::memset(trans_id, 0, WLAN_SA_QUERY_TR_ID_LEN);

    // Process ToDS and FromDS Bits For Correct Addresses, Visual Output
    if(!GetToDS(ie80211_un) && !GetFromDS(ie80211_un)) { // 0 0
        flow   = "\nFlow:                     STA -> STA (IBSS/DLS, Ad-hoc)";
        saddr1 = "\nDestination Address:      ";
        saddr2 = "\nSource Address:           ";
        saddr3 = "\nBasic Service Set ID:     ";
        addr_count_is_3 = true;
    }
    else if(!GetToDS(ie80211_un) &&  GetFromDS(ie80211_un)) { // 0 1
        flow   = "\nFlow:                     AP -> STA";       
        saddr1 = "\nDestination Address:      ";
        saddr2 = "\nBasic Service Set ID:     ";
        saddr3 = "\nSource Address:           ";
        addr_count_is_3 = true;
    }
    else if( GetToDS(ie80211_un) && !GetFromDS(ie80211_un)) { // 1 0
        flow   = "\nFlow:                     STA -> AP";       
        saddr1 = "\nBasic Service Set ID:     ";
        saddr2 = "\nSource Address:           ";
        saddr3 = "\nDestination Address:      ";
        addr_count_is_3 = true;
    }
    else if( GetToDS(ie80211_un) &&  GetFromDS(ie80211_un)) { // 1 1
        flow   = "\nFlow:                     STA -> AP -> STA (WDS, bridge)";
        saddr1 = "\nReceiver Address:         ";
        saddr2 = "\nTransmitter Address:      ";
        saddr3 = "\nDestination Address:      ";
        saddr4 = "\nSource Address:           ";
        addr_count_is_3 = false; // expicit, incase it changed
    }
//  else shouldn't happen

    // Print IEEE 802.11 Header
    ofs << "\n~~~ieee 802.11 Header~~~" // all frames have FC so use any in our union
        << "\nFrame Control Total:      " << le16toh(ie80211_un->ieee80211_3.frame_control)
        << "\nProtocol:                 " << (unsigned)GetProtocol(ie80211_un)
        << "\nTo   Distr System Flag:   " << (GetToDS(ie80211_un)     ? '1' : '0')
        << "\nFrom Distr System Flag:   " << (GetFromDS(ie80211_un)   ? '1' : '0')
        << "\nMore Fragments Flag:      " << (GetMoreFlag(ie80211_un) ? '1' : '0')
        << "\nRetry Flag:               " << (GetRetry(ie80211_un)    ? '1' : '0')
        << "\nPower Management Flag:    " << (GetPwrMgt(ie80211_un)   ? '1' : '0')
        << "\nMore Data Flag:           " << (GetMoreData(ie80211_un) ? '1' : '0')
        << "\nPrivacy Flag (WPA/WEP...) " << (GetPrivacy(ie80211_un)  ? '1' : '0')
        << "\nOrder Flag (802.11n):     " << (GetOrder(ie80211_un)    ? '1' : '0'); // 802.11n
    
    // Process Frame Type
    ofs << "\nFrame Type:               ";   
    switch(GetFrameType(ie80211_un)) {
    // Management Frames
    case WIFI_MGMT_FRAME:
        // Print
        ofs << "0:  Management Frame"
            << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_mgmt.duration)           
            << "\nSource Address:           "
            << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_mgmt.sa, (char*)sa) // need reentrants
            << "\nDestination Address:      "
            << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_mgmt.da, (char*)da)
            << "\nBSSID:                    "
            << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_mgmt.bssid, (char*)bssid)
            << "\nSequence Control:         " << SEQ_NUM(ie80211_un->ieee80211_mgmt.seq_ctrl)
            << "\nFragment Offset:          " << FRAG_NUM(ie80211_un->ieee80211_mgmt.seq_ctrl);

        // Process Frame Subtype
        ofs << "\nFrame Subtype:            ";
        switch(GetFrameSubType(ie80211_un)) {
        case WIFI_ASSOCREQ:
            ofs << "0:  Association Request"
                << "\nCapability Info:          "
                << le16toh(ie80211_un->ieee80211_mgmt.u.assoc_req.capab_info)
                << "\nListen Interval:          "
                << le16toh(ie80211_un->ieee80211_mgmt.u.assoc_req.listen_interval)
                << "\n~Information Element~"
                << "\nElement ID:               "
                << (unsigned)ie80211_un->ieee80211_mgmt.u.assoc_req.ie[0].ie_gen.id
                << "\nLength:                   "
                << (unsigned)ie80211_un->ieee80211_mgmt.u.assoc_req.ie[0].ie_gen.len;

            // Process Information Element
            switch((unsigned)ie80211_un->ieee80211_mgmt.u.assoc_req.ie[0].ie_gen.id) {
                case 0: // SSID
                    ofs << "\nSSID:                     ";
                    for(std::size_t i = 0; i < (unsigned)ie80211_un->ieee80211_mgmt.u.assoc_req.ie[0].ie_gen.len; ++i)
                        ofs << ie80211_un->ieee80211_mgmt.u.assoc_req.ie[0].ie_gen.ssid[i];
                    break;
                default:
                    break;
            };
            ////////////////variable
            break;
        case WIFI_ASSOCRSP:
            ofs << "1:  Association Response"
                << "\nCapability Info:          "
                << le16toh(ie80211_un->ieee80211_mgmt.u.assoc_resp.capab_info)
                << "\nStatus Code:              "
                << le16toh(ie80211_un->ieee80211_mgmt.u.assoc_resp.status_code);
            print80211Status(ie80211_un->ieee80211_mgmt.u.assoc_resp.status_code);
            ofs << "\nAssociation ID:           "
                << le16toh(ie80211_un->ieee80211_mgmt.u.assoc_resp.aid);
            break;
        case WIFI_REASSOCREQ:
            ofs << "2:  Reassociation Request"
                << "\nCapability Info:          "
                << le16toh(ie80211_un->ieee80211_mgmt.u.reassoc_req.capab_info)
                << "\nListen Interval:          "
                << le16toh(ie80211_un->ieee80211_mgmt.u.reassoc_req.listen_interval)
                << "\nCurrent Access Point:     "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_mgmt.u.reassoc_req.current_ap, (char*)cur_ap)
                << "\n~Information Element~"
                << "\nElement ID:               "
                << (unsigned)ie80211_un->ieee80211_mgmt.u.reassoc_req.ie[0].ie_gen.id
                << "\nLength:                   "
                << (unsigned)ie80211_un->ieee80211_mgmt.u.reassoc_req.ie[0].ie_gen.len;

            // Process Information Element
            switch((unsigned)ie80211_un->ieee80211_mgmt.u.reassoc_req.ie[0].ie_gen.id) {
                case 0: // SSID
                    ofs << "\nSSID:                     ";
                    for(std::size_t i = 0; i < (unsigned)ie80211_un->ieee80211_mgmt.u.reassoc_req.ie[0].ie_gen.len; ++i)
                        ofs << ie80211_un->ieee80211_mgmt.u.reassoc_req.ie[0].ie_gen.ssid[i];
                    break;
                default:
                    break;
            };
            ////////////////variable
            break;
        case WIFI_REASSOCRSP:
            ofs << "3:  Reassociation Response"
                << "\nCapability Info:          "
                << le16toh(ie80211_un->ieee80211_mgmt.u.reassoc_resp.capab_info)
                << "\nStatus Code:              "
                << le16toh(ie80211_un->ieee80211_mgmt.u.reassoc_resp.status_code);
            print80211Status(ie80211_un->ieee80211_mgmt.u.reassoc_resp.status_code);
            ofs << "\nAssociation ID:           "
                << le16toh(ie80211_un->ieee80211_mgmt.u.reassoc_resp.aid);
            ////////////////variable
            break;
        case WIFI_PROBEREQ:
            ofs << "4:  Probe Request"
                << "\n~Information Element~"
                << "\nElement ID:               "
                << (unsigned)ie80211_un->ieee80211_mgmt.u.probe_req.ie[0].ie_gen.id
                << "\nLength:                   "
                << (unsigned)ie80211_un->ieee80211_mgmt.u.probe_req.ie[0].ie_gen.len;

            // Process Information Element
            switch((unsigned)ie80211_un->ieee80211_mgmt.u.probe_req.ie[0].ie_gen.id) {
                case 0: // SSID
                    ofs << "\nSSID:                     ";
                    for(std::size_t i = 0; i < (unsigned)ie80211_un->ieee80211_mgmt.u.probe_req.ie[0].ie_gen.len; ++i)
                        ofs << ie80211_un->ieee80211_mgmt.u.probe_req.ie[0].ie_gen.ssid[i];
                    break;
                default:
                    break;
            };
            ////////////////variable
            break;
        case WIFI_PROBERSP:
            ofs << "4:  Probe Response"
                << "\nTimestamp:                "
                << (long long)le64toh(ie80211_un->ieee80211_mgmt.u.probe_resp.timestamp)
                << "\nBeacon Interval:          "
                << le16toh(ie80211_un->ieee80211_mgmt.u.probe_resp.beacon_int)
                << "\nCapability Info:          "
                << le16toh(ie80211_un->ieee80211_mgmt.u.probe_resp.capab_info)
                << "\n~Information Element~"
                << "\nElement ID:               "
                << (unsigned)ie80211_un->ieee80211_mgmt.u.probe_resp.ie[0].ie_gen.id
                << "\nLength:                   "
                << (unsigned)ie80211_un->ieee80211_mgmt.u.probe_resp.ie[0].ie_gen.len;

            // Process Information Element
            switch((unsigned)ie80211_un->ieee80211_mgmt.u.probe_resp.ie[0].ie_gen.id) {
                case 0: // SSID
                    ofs << "\nSSID:                     ";
                    for(std::size_t i = 0; i < (unsigned)ie80211_un->ieee80211_mgmt.u.probe_resp.ie[0].ie_gen.len; ++i)
                        ofs << ie80211_un->ieee80211_mgmt.u.probe_resp.ie[0].ie_gen.ssid[i];
                    break;
                default:
                    break;
            };
            ////////////////variable
            break;
        case WIFI_BEACON: {
            ofs << "8:  Beacon"
                << "\nTimestamp:                "
                << (long long)le64toh(ie80211_un->ieee80211_mgmt.u.beacon.timestamp)
                << "\nBeacon Interval:          "
                << (((float)(le16toh(ie80211_un->ieee80211_mgmt.u.beacon.beacon_int)) * 1024.00) / 1000.00)
                << " ms"
                << "\nCapability Info:          "
                << le16toh(ie80211_un->ieee80211_mgmt.u.beacon.capab_info)
                << "\n\n~MGMT Information Elements~";

            // Process Information Element
            ieee80211_ie *ieStart = (ieee80211_ie*)((cuchar_cptr)ie80211_un->ieee80211_mgmt.u.beacon.ie);
            ieee80211_ie *ie      = (ieee80211_ie*)((cuchar_cptr)ieStart);
            for(unsigned oset = 0; oset < len;) {
                // Process EID
                ofs << "\nElement ID:               " << (unsigned)ie->ie_gen.id;               
                switch((unsigned)ie->ie_gen.id) {
                    case WLAN_MGMT_IE_SSID:
                        ofs << ": SSID"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nSSID:                     ";

                        // Print SSID
                        for(std::size_t j = 0; j < (unsigned)ie->ie_gen.len; ++j)
                            ofs << ie->ie_gen.ssid[j];
                        break;
                    case WLAN_MGMT_IE_RATES:
                        ofs << ": Rates"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nIE Rates:                 ";

                        // Print Rates
                        for(std::size_t j = 0; j < (unsigned)ie->ie_gen.len; ++j) {
                            ofs << ((float)(unsigned)((ie->ie_gen.rates[j]) & 0x7F) * 500.00) / 1000.00 << " Mb/s" // 500 Kbps units
                                << ((ie->ie_gen.rates[j] & 0x80) ? " - Basic" : "");
                            // Check Newline Cutoff
                            if(j != (unsigned)ie->ie_gen.len - 1)
                                ofs << "\n                          ";
                        }
                        break;
                        case WLAN_MGMT_IE_FH_PARAM:
                        ofs << ": FH Parameter Set"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_DS_PARAM:
                        ofs << ": DS Parameter Set(Channel No.)"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nCurrent Channel:          " << (unsigned)ie->ds_param.cur_chan;
                        break;
                        case WLAN_MGMT_IE_CF_PARAM:
                        ofs << ": CF Parameter Set"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_TIM:
                        ofs << ": Traffic Indication Map(TIM)"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nDTIM Count:               " << (unsigned)ie->tim.DTIM_count
                            << "\nDTIM Period:              " << (unsigned)ie->tim.DTIM_period
                            << "\nBitmap Control:           "
                            << ((ie->tim.bitmap_ctrl & 0x80) ? ": Buffered Data" : "No Buffered Data")
                            << "\nPartial Virtual Bitmap:   " << (unsigned)ie->tim.partial_virtual_bitmap;////////////////////////fix from book mit need to be variable[0]
                        break;
                    case WLAN_MGMT_IE_IBSS_PARAM:
                        ofs << ": IBSS Parameter Set"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_COUNTRY: // 802.11d
                        ofs << ": Country"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nCountry:                  ";
                        break;
                    case WLAN_MGMT_IE_HOP_PARAM: // 802.11d
                        ofs << ": HOP Parameter Set"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_HOP_TABLE: // 802.11d
                        ofs << ": HOP Table"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_REQUEST: // 802.11d
                        ofs << ": Request"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nRequested IEs:            ";

                        // Print Requested IEs For Probe Response Frame
                        for(std::size_t j = 0; j < (unsigned)ie->ie_gen.len; ++j) ///////////add names
                            ofs << (unsigned)ie->ie_gen.request[j] << ' ';
                        break;
                    case WLAN_MGMT_IE_QBSS_LOAD:
                        ofs << ": QBSS Load"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_EDCA_PARAM:
                        ofs << ": EDCA Parameter Set"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_TSPEC:
                        ofs << ": TSPEC"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_TCLAS:
                        ofs << ": TCLAS"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_SCEDULE:
                        ofs << ": Schedule"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_CHALLENGE_TEXT:
                        ofs << ": Challenge Text(Shared Key Auth)"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nChallenge Text:           ";

                            // Print Challenge Text For Association Frames(Shared Key Auth)
                            for(std::size_t j = 0; j < (unsigned)ie->ie_gen.len; ++j)
                                ofs << (char)ie->ie_gen.challenge_text[j];
                        break;
                    case WLAN_MGMT_IE_POWER_CAPAB: // 802.11h
                        ofs << ": Power Capabilities"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nMin TX Power:             " << (unsigned)ie->power_capab.min_txpwr << " dbm"
                            << "\nMax TX Power:             " << (unsigned)ie->power_capab.max_txpwr << " dbm";
                        break;
                    case WLAN_MGMT_IE_TPC_REQUEST: // 802.11h
                        ofs << ": TPC Request"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len; // 0 len, nothing follows
                        break;
                    case WLAN_MGMT_IE_TPC_REPORT: // 802.11h
                         ofs << ": TPC Report"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nMin TX Power:             " << (unsigned)ie->tpc_report.tx_power    << " dbm"
                            << "\nMax TX Power:             " << (unsigned)ie->tpc_report.link_margin << " dbm";
                        break;
                    case WLAN_MGMT_IE_CHANNELS: // 802.11h
                        ofs << ": Channels"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_CHANNEL_SWITCH: // 802.11h
                        ofs << ": Channel Switch"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_MEASURE_REQUEST: // 802.11h
                        ofs << ": Radio Measurement Request"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_MEASURE_REPORT: // 802.11h
                        ofs << ": Radio Measurement Report"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_QUITE: // 802.11h
                        ofs << ": Quite"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_IBSS_DFS: // 802.11h
                        ofs << ": IBSS DFS Parameters"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_ERP:      // 802.11g                       
                    case WLAN_MGMT_IE_ERP_INFO: // 802.11g
                        ofs << ": ERP(PHY-Level Flags)"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nERP Info Sum:             " << (unsigned)ie->ie_gen.erp_info
                            << "\nBarker Preamble Mode:     "
                            << (ie->ie_gen.erp_info & 0x04 ? '1' : '0')
                            << "\nUse Protection:           "
                            << (ie->ie_gen.erp_info & 0x02 ? '1' : '0')
                            << "\nNon-ERP Present:          "
                            << (ie->ie_gen.erp_info & 0x01 ? '1' : '0');
                        break;
                    case WLAN_MGMT_IE_TS_DELAY:
                        ofs << ": TS Delay"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_TCLAS_PROCESSING:
                        ofs << ": TCLAS Processing"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_HT_CAPABILITY: // 802.11n
                        ofs << ": HT Capabilities"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nHT Capabilities Info Sum: " << le16toh(ie->ht_capab.capab_info)
                            << "\nLDPC Codeing Capability:  "
                            << (le16toh(ie->ht_capab.capab_info) & 0x0001 ? '1' : '0')
                            << "\nChannel Width Set:        "
                            << (le16toh(ie->ht_capab.capab_info) & 0x0002 ? "1: 20Mhz And 40Mhz Operation" 
                              :                                             "0: 20Mhz Only Operation")
                            << "\nSpatial Multiplexing PS:  " << ((le16toh(ie->ht_capab.capab_info) & 0x000C) >> 2)
                            << (((~le16toh(ie->ht_capab.capab_info) & 0x000C) >> 2) == 0x0003 ? ": Static SMPS Mode" // 00
                             :   ((le16toh(ie->ht_capab.capab_info) & 0x000C) >> 2) == 0x0001 ? ": Dynamic SMPS Mode"
                             :   ((le16toh(ie->ht_capab.capab_info) & 0x000C) >> 2) == 0x0002 ? ": Reserved"
                             :   ((le16toh(ie->ht_capab.capab_info) & 0x000C) >> 2) == 0x0003 ? ": SMPS Mode Disabled"
                             : ": Unknown SMPS Mode") // shouldn't happen
                            << "\nHT-Greenfield:            "
                            << (le16toh(ie->ht_capab.capab_info) & 0x0010 ? '1' : '0')
                            << "\nShort GI For 20Mhz:       "
                            << (le16toh(ie->ht_capab.capab_info) & 0x0020 ? '1' : '0')
                            << "\nShort GU For 40Mhz:       "
                            << (le16toh(ie->ht_capab.capab_info) & 0x0040 ? '1' : '0')
                            << "\nTX STBC:                  "
                            << (le16toh(ie->ht_capab.capab_info) & 0x0080 ? '1' : '0')
                            << "\nRX STBC:                  " << ((le16toh(ie->ht_capab.capab_info) & 0x0300) >> 8)
                            << (((~le16toh(ie->ht_capab.capab_info) & 0x0300) >> 8) == 0x0003 ? ": Not Supported" // 00
                             :   ((le16toh(ie->ht_capab.capab_info) & 0x0300) >> 8) == 0x0001 ? ": 1 Spatial Stream"
                             :   ((le16toh(ie->ht_capab.capab_info) & 0x0300) >> 8) == 0x0002 ? ": 1 or 2 Spatial Streams"
                             :   ((le16toh(ie->ht_capab.capab_info) & 0x0300) >> 8) == 0x0003 ? ": 1, 2, or 3 Spatial Streams"
                             : ": Unknown Spatial Stream") // shouldn't happen
                            << "\nHT-Delayed Block Ack:     " // DELBA
                            << (le16toh(ie->ht_capab.capab_info) & 0x0400 ? '1' : '0')
                            << "\nMax A-MSDU Length:        "
                            << (le16toh(ie->ht_capab.capab_info) & 0x0800 ? '1' : '0')
                            << "\nDSSS/CCK Mode In 40Mhz:   "
                            << (le16toh(ie->ht_capab.capab_info) & 0x1000 ? '1' : '0')
                            << "\nPSMP Support:             "
                            << (le16toh(ie->ht_capab.capab_info) & 0x2000 ? '1' : '0')
                            << "\n40Mhz Intolerant:         "
                            << (le16toh(ie->ht_capab.capab_info) & 0x4000 ? '1' : '0')
                            << "\nL-SIG TXOP Protection:    "
                            << (le16toh(ie->ht_capab.capab_info) & 0x8000 ? '1' : '0')
                            << "\nA-MPDU Settings Sum:      "
                            << (unsigned)ie->ht_capab.a_mpdu_param
                            << "\nMax A-MPDU Size:          " << (le16toh(ie->ht_capab.a_mpdu_param) & 0x03)
                            << (~le16toh(ie->ht_capab.a_mpdu_param) & 0x03 == 0x03 ? ": 8KB" // 00
                              :  le16toh(ie->ht_capab.a_mpdu_param) & 0x03 == 0x01 ? ": 16KB"
                              :  le16toh(ie->ht_capab.a_mpdu_param) & 0x03 == 0x02 ? ": 36KB"
                              :  le16toh(ie->ht_capab.a_mpdu_param) & 0x03 == 0x03 ? ": 64KB"
                              : ": Unknown Size") // shouldn't happen
                            << "\nMin MPDU Start Spacing:   " << ((le16toh(ie->ht_capab.a_mpdu_param) & 0x1C) >> 2)
                            << (((~le16toh(ie->ht_capab.a_mpdu_param) & 0x1C) >> 2) == 0x07 ? ": No Restrictions" // 00
                              :  ((le16toh(ie->ht_capab.a_mpdu_param) & 0x1C) >> 2) == 0x01 ? ": 1/4 us"
                              :  ((le16toh(ie->ht_capab.a_mpdu_param) & 0x1C) >> 2) == 0x02 ? ": 1/2 us"
                              :  ((le16toh(ie->ht_capab.a_mpdu_param) & 0x1C) >> 2) == 0x03 ? ": 1 us"
                              :  ((le16toh(ie->ht_capab.a_mpdu_param) & 0x1C) >> 2) == 0x04 ? ": 2 us"
                              :  ((le16toh(ie->ht_capab.a_mpdu_param) & 0x1C) >> 2) == 0x05 ? ": 4 us"
                              :  ((le16toh(ie->ht_capab.a_mpdu_param) & 0x1C) >> 2) == 0x06 ? ": 8 us"
                              :  ((le16toh(ie->ht_capab.a_mpdu_param) & 0x1C) >> 2) == 0x07 ? ": 16 us"
                              : ": Unknown Start Spacing") // shouldn't happen
                            << "\nMPDU Reserved Bit Sum:    " << ((le16toh(ie->ht_capab.a_mpdu_param) & 0xE0) >> 5);
                            break;
                    case WLAN_MGMT_IE_QOS_CAPABILITY:
                        ofs << ": QOS Capabilities"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_RSN: // 802.11i
                        ofs << ": Robust Security Network(WLAN)"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nVersion:                  " << (unsigned)ie->rsn.version
                            << "\n";
                        break;
                    case WLAN_MGMT_IE_EXT_RATES: // 802.11g
                        ofs << ": Extension Rates"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nExtended Rates:           ";

                        // Print Rates
                        for(std::size_t j = 0; j < (unsigned)ie->ie_gen.len; ++j) {
                            ofs << (((float)(unsigned)((ie->ie_gen.rates[j]) & 0x7F) * 500.00) / 1000.00)
                                << " Mb/s" // 500 Kbps units
                                << ((ie->ie_gen.rates[j] & 0x80) ? " - Basic" : "");
                            // Check Newline Cutoff
                            if(j != (unsigned)ie->ie_gen.len - 1)
                                ofs << "\n                          ";
                        }
                        break;
                    case WLAN_MGMT_IE_POWER_CONSTRAINT_OLD: // 802.11h                       
                    case WLAN_MGMT_IE_POWER_CONSTRAINT:     // 802.11h
                        ofs << ": Power Constraint"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nLocal Power Constraint:   " << (unsigned)ie->ie_gen.power_constraint
                            << " db";
                        break;
                    case WLAN_MGMT_IE_MOBILITY_DOMAIN: // 802.11r
                        ofs << ": Mobility Domain"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_HT_OPERATION: // 802.11n
                        ofs << ": HT Operations"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_RM_ENABLED_CAPAB:
                        ofs << ": RM Enabled Capabilities"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_20_40_BSS_COEX: // 802.11n
                        ofs << ": 20/40 BSS Coexistence"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_OVERLAP_BSS_SCAN: // 802.11n
                        ofs << ": Overlapping BSS Scan"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_EXT_CAPABILITY:
                        ofs << ": Extended Capabilities(CIF)"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_CISCO_PROPERTY: // cisco proprietary
                        ofs << ": Cisco Proprietary"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_CISCO_SYSTEMS: // cisco systems
                        ofs << ": Cisco Systems"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_VHT_CAPABILITY: // 802.11ac
                        ofs << ": VHT Capabilities"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_VHT_OPERATION: // 802.11ac
                        ofs << ": VHT Operations"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_VHT_TRANSMIT_PWR: // 802.11ac
                        ofs << ": VHT Transmit Power"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                    case WLAN_MGMT_IE_VENDOR:
                        ofs << ": Vendor Specific"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len
                            << "\nOUI:                      ";
                        break;
                    default: // unknown, check online
                        ofs << ": Unknown IE"
                            << "\nLength:                   " << (unsigned)ie->ie_gen.len;
                        break;
                };
                oset += (unsigned)ie->ie_gen.len + 2; // 2 Bs, id and len
                ie    = (ieee80211_ie*)((cuchar_cptr)ieStart + oset);
                ofs << '\n';
            }
            ///////////////////variable
            break;
        }
        case WIFI_ATIM:
            ofs << "9:  Announcement Traffic Indication Message(ATIM)";
            break;
        case WIFI_DISASSOC:
            ofs << "10: Disassociation"
                << "\nReason Code:              "
                << le16toh(ie80211_un->ieee80211_mgmt.u.disassoc.reason_code);
            print80211Reason(ie80211_un->ieee80211_mgmt.u.disassoc.reason_code);
            break;
        case WIFI_AUTH:
            ofs << "11: Authentication"
                << "\nAuth Algorithm:           "
                << le16toh(ie80211_un->ieee80211_mgmt.u.auth.auth_alg)
                << "\nAuth Transaction:         "
                << le16toh(ie80211_un->ieee80211_mgmt.u.auth.auth_transaction)
                << "\nStatus Code:              "
                << le16toh(ie80211_un->ieee80211_mgmt.u.auth.status_code);
            print80211Status(ie80211_un->ieee80211_mgmt.u.auth.status_code);
            //////////////////variable
            break;
        case WIFI_DEAUTH:
            ofs << "12: Deauthentication"
                << "\nReason Code:              "
                << le16toh(ie80211_un->ieee80211_mgmt.u.deauth.reason_code);
            print80211Reason(ie80211_un->ieee80211_mgmt.u.deauth.reason_code);
            break;
        case WIFI_ACTION:
            ofs << "13: Action"
                << "\nCategory:                 "
                << (unsigned)ie80211_un->ieee80211_mgmt.u.action.category;
            print80211ActionCat((unsigned)ie80211_un->ieee80211_mgmt.u.action.category);
            ofs << "\nAction Code:              " // any action struct works, e.g. wme_action
                << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.wme_action.action_code;

            // Process Action Category
            switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.category) {
            case WLAN_CATEGORY_SPECTRUM_MGMT: // Spectrum
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_ACTION_SPCT_MSR_REQ:
                    ofs << ": Measurement Request"
                        << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.dialog_token
                        << "\nElement ID:               "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.element_id
                        << "\nLength:                   "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.length
                        << "\nToken:                    "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.token
                        << "\nMode:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.mode
                        << "\nType:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.type;
                    //////////////////request variable 
                    break;
                case WLAN_ACTION_SPCT_MSR_RPRT:
                    ofs << ": Measurement Report"
                        << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.dialog_token
                        << "\nElement ID:               "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.element_id
                        << "\nLength:                   "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.length
                        << "\nToken:                    "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.token
                        << "\nMode:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.mode         
                        << "\nType:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.type;
                    //////////////////request variable 
                    break;
                case WLAN_ACTION_SPCT_TPC_REQ:
                    ofs << ": Transmit Power Control Request";
                    break;
                case WLAN_ACTION_SPCT_TPC_RPRT:
                    ofs << ": Transmit Power Control Report"
                        << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.tpc_report.dialog_token
                        << "\nTPC Element ID:           "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.tpc_report.tpc_elem_id
                        << "\nTPC Element Length:       "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.tpc_report.tpc_elem_length
                        << "\nTX Power:                 "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.tpc_report.tpc.tx_power
                        << "\nLink Margin:              "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.tpc_report.tpc.link_margin;
                    break;
                case WLAN_ACTION_SPCT_CHL_SWITCH:
                    ofs << ": Channel Switch";
                    //////////////////variable 
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                }; // spectrum switch end
                break;
            case WLAN_CATEGORY_QOS: // QOS
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_ACTION_QOS_ADDTS_REQ:
                    ofs << ": Add Traffic Stream Request";
                    break;
                case WLAN_ACTION_QOS_ADDTS_RESP:
                    ofs << ": Add Traffic Stream Response";
                    break;
                case WLAN_ACTION_QOS_DELTS:
                    ofs << ": Delete Traffic Stream";
                    break;
                case WLAN_ACTION_QOS_SHEDULE:
                    ofs << ": Schedule";
                    break;
                case WLAN_ACTION_QOS_MAP_CONFIGURE:
                    ofs << ": Map Configuration";
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_DLS: // DLS
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_ACTION_DLS_REQ:
                    ofs << ": DLS Request";
                    break;
                case WLAN_ACTION_DLS_RESP:
                    ofs << ": DLS Response";
                    break;
                case WLAN_ACTION_DLS_TEARDOWN:
                    ofs << ": DLS Teardown";
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_BACK: // BACK
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_ACTION_BACK_ADDBA_REQ:
                    ofs << ": Add Block-Ack Request(ADDBA)"
                        << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.dialog_token
                        << "\nCapability:               "
                        << le16toh(ie80211_un->ieee80211_mgmt.u.action.u.addba_req.capab)
                        << "\nTimeout:                  "
                        << le16toh(ie80211_un->ieee80211_mgmt.u.action.u.addba_req.timeout)
                        << "\nStart Sequence Number:    "
                        << le16toh(ie80211_un->ieee80211_mgmt.u.action.u.addba_req.start_seq_num);
                    break;
                case WLAN_ACTION_BACK_ADDBA_RESP:
                    ofs << ": Add Block-Ack Response(ADDBA)"                                   
                        << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_resp.dialog_token
                        << "\nStatus Code:              "
                        << le16toh(ie80211_un->ieee80211_mgmt.u.action.u.addba_resp.status);
                    print80211Status(ie80211_un->ieee80211_mgmt.u.action.u.addba_resp.status);
                    ofs << "\nCapability:               "
                        << le16toh(ie80211_un->ieee80211_mgmt.u.action.u.addba_resp.capab)
                        << "\nTimeout:                  "
                        << le16toh(ie80211_un->ieee80211_mgmt.u.action.u.addba_resp.timeout);
                    break;
                case WLAN_ACTION_BACK_ADDBA_DELBA:
                    ofs << ": Delayed Block-Ack(DELBA)"
                        << "\nParameters:               "
                        << le16toh(ie80211_un->ieee80211_mgmt.u.action.u.delba.params)
                        << "\nReason Code:              "
                        << le16toh(ie80211_un->ieee80211_mgmt.u.action.u.delba.reason_code);
                    print80211Reason(ie80211_un->ieee80211_mgmt.u.action.u.delba.reason_code);
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_PUBLIC: // Public
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_PUB_ACTION_EXT_CHANSW_ANN:
                    ofs << ": External Channel Switch Announcement"
                        << "\nMode:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.ext_chan_switch.data.mode
                        << "\nNew Operating Class:      "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.ext_chan_switch.data.new_operating_class
                        << "\nNew Channel Number:       "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.ext_chan_switch.data.new_ch_num
                        << "\nCount:                    "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.ext_chan_switch.data.count;
                    //////////////////variable
                    break;
                case WLAN_PUB_ACTION_TDLS_DISCOVER_RES:
                    ofs << ": TDLS Discovery Response"
                        << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.tdls_discover_resp.dialog_token
                        << "\nCapability:               "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.tdls_discover_resp.capability;
                    //////////////////variable
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_RADIO_MEASUREMENT: // Radio Measurement
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_ACTION_RADIO_MEAS_REQ:
                    ofs << ": Measurement Request"
                        << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.dialog_token
                        << "\nElement ID:               "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.element_id
                        << "\nLength:                   "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.length
                        << "\nToken:                    "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.token
                        << "\nMode:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.mode
                        << "\nType:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.type;
                    //////////////////request variable 
                    break;
                case WLAN_ACTION_RADIO_MEAS_RPRT:
                    ofs << ": Measurement Report"
                        << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.dialog_token
                        << "\nElement ID:               "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.element_id
                        << "\nLength:                   "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.length
                        << "\nToken:                    "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.token
                        << "\nMode:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.mode
                        << "\nType:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.type;
                    //////////////////request variable 
                    break;
                case WLAN_ACTION_RADIO_MEAS_LINK_MEAS_REQ:
                    ofs << ": Link Measurement Request"               << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.dialog_token
                        << "\nElement ID:               "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.element_id
                        << "\nLength:                   "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.length
                        << "\nToken:                    "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.token
                        << "\nMode:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.mode
                        << "\nType:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.type;
                    //////////////////request variable 
                    break;
                case WLAN_ACTION_RADIO_MEAS_LINK_MEAS_RPRT:
                    ofs << ": Link Measurement Report"
                        << "\nDialog Token:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.dialog_token
                        << "\nElement ID:               "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.element_id
                        << "\nLength:                   "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.length    
                        << "\nToken:                    "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.token
                        << "\nMode:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.mode
                        << "\nType:                     "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.measurement.msr_elem.type;
                    //////////////////request variable 
                    break;
                case WLAN_ACTION_RADIO_MEAS_NEIGHBOR_RPRT_REQ:  // 802.11k
                    ofs << ": Neighbor Report Request";
                    break;
                case WLAN_ACTION_RADIO_MEAS_NEIGHBOR_RPRT_RESP: // 802.11k
                    ofs << ": Neighbor Report Response";
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                }; // radio measurement switch end
                break;
            case WLAN_CATEGORY_HT: // HT 802.11n
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_HT_ACTION_NOTIFY_CHANWIDTH:
                    ofs << ": Notify Channel Width"
                        << "\nChannel Width:            "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.ht_notify_cw.chanwidth;
                    break;
                case WLAN_HT_ACTION_SMPS:
                    ofs << ": Spatial Multiplexing Power Save(SMPS)"
                        << "\nSMPS Control:             "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.ht_smps.smps_control;;
                    break;
                case WLAN_HT_ACTION_PSMP:
                    ofs << ": Power Save Multi-Poll(PSMP)";
                    break;
                case WLAN_HT_ACTION_PCO_PHASE:
                    ofs << ": Phased Coexistence Operation(PCO) Phase";
                    break;
                case WLAN_HT_ACTION_CSI:
                    ofs << ": Channel State Information";
                    break;
                case WLAN_HT_ACTION_NONCOMPRESSED_BF:
                    ofs << ": Non-Compressed Beamforming";
                    break;
                case WLAN_HT_ACTION_COMPRESSED_BF:
                    ofs << ": Compressed Beamforming";
                    break;
                case WLAN_HT_ACTION_ASEL_IDX_FEEDBACK:
                    ofs << ": Antenna Selection Index Feedback";
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;       
            case WLAN_CATEGORY_SA_QUERY: // SA Query
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_ACTION_SA_QUERY_REQUEST:
                    // Fill Buffer
                    std::snprintf((char*)trans_id, WLAN_SA_QUERY_TR_ID_PRINT_LEN, "%.2X:%.2X",
                                 ie80211_un->ieee80211_mgmt.u.action.u.sa_query.trans_id[0],
                                 ie80211_un->ieee80211_mgmt.u.action.u.sa_query.trans_id[1]);

                    ofs << ": Query Request"
                        << "\nTransmission ID:          " << trans_id;
                    break;
                case WLAN_ACTION_SA_QUERY_RESPONSE:
                    // Fill Buffer
                    std::snprintf((char*)trans_id, WLAN_SA_QUERY_TR_ID_PRINT_LEN, "%.2X:%.2X",
                                 ie80211_un->ieee80211_mgmt.u.action.u.sa_query.trans_id[0],
                                 ie80211_un->ieee80211_mgmt.u.action.u.sa_query.trans_id[1]);

                    ofs << ": Query Response"
                        << "\nTransmission ID:          " << trans_id;
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
               break;
            case WLAN_CATEGORY_PROTECTED_DUAL_OF_ACTION: // Protected Dual Of Action
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_TDLS: // TDLS 802.11z
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_TDLS_SETUP_REQUEST:
                    ofs << ": Setup Request";
                    break;
                case WLAN_TDLS_SETUP_RESPONSE:
                    ofs << ": Setup Response";
                    break;
                case WLAN_TDLS_SETUP_CONFIRM:
                    ofs << ": Setup Confirm";
                    break;
                case WLAN_TDLS_TEARDOWN:
                    ofs << ": Teardown";
                    break;
                case WLAN_TDLS_PEER_TRAFFIC_INDICATION:
                    ofs << ": Peer Traffic Indication";
                    break;
                case WLAN_TDLS_CHANNEL_SWITCH_REQUEST:
                    ofs << ": Channel Switch Request";
                    break;
                case WLAN_TDLS_CHANNEL_SWITCH_RESPONSE:
                    ofs << ": Channel Switch Response"; 
                    break;
                case WLAN_TDLS_PEER_PSM_REQUEST:
                    ofs << ": Peer PSM Request";
                    break; 
                case WLAN_TDLS_PEER_PSM_RESPONSE:
                    ofs << ": Peer Power-Saveing Mode";
                    break;
                case WLAN_TDLS_PEER_TRAFFIC_RESPONSE:
                    ofs << ": Peer Traffic Response";
                    break;
                case WLAN_TDLS_DISCOVERY_REQUEST:
                    ofs << ": Discovery Request";
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                }; // TDLS Switch end
                break;
            case WLAN_CATEGORY_MESH_ACTION: // MESH 802.11s
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_MESH_ACTION_LINK_METRIC_REPORT:
                    ofs << ": Link Metric Report";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_HWMP_PATH_SELECTION:
                    ofs << ": HWMP Path Selection";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_GATE_ANNOUNCEMENT:
                    ofs << ": Gate Announcement";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_CONGESTION_CONTROL_NOTIFICATION:
                    ofs << ": Congestion Control Notification";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_MCCA_SETUP_REQUEST:
                    ofs << ": MCCA Setup Request";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_MCCA_SETUP_REPLY:
                    ofs << ": MCCA Setup Reply";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_MCCA_ADVERTISEMENT_REQUEST:
                    ofs << ": MCCA Advertisement Request";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_MCCA_ADVERTISEMENT:
                    ofs << ": MCCA Advertisement";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_MCCA_TEARDOWN:
                    ofs << ": MCCA Teardown";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_TBTT_ADJUSTMENT_REQUEST:
                    ofs << ": TBTT Adjustment Request";
                    /////////////variable
                    break;
                case WLAN_MESH_ACTION_TBTT_ADJUSTMENT_RESPONSE:
                    ofs << ": TBTT Adjustment Response";
                    /////////////variable
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                }; // MESH switch end
                break;
            case WLAN_CATEGORY_MULTIHOP_ACTION: // Multi-Hop
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_SELF_PROTECTED: // Self Protecte 
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_SP_RESERVED:
                    ofs << ": Reserved";
                    /////////////variable
                    break;
                case WLAN_SP_MESH_PEERING_OPEN:
                    ofs << ": Peering Open";
                    /////////////variable
                    break;
                case WLAN_SP_MESH_PEERING_CONFIRM:
                    ofs << ": Peering Confirm";
                    /////////////variable
                    break;
                case WLAN_SP_MESH_PEERING_CLOSE:
                    ofs << ": Peering Close";
                    /////////////variable
                    break;
                case WLAN_SP_MGK_INFORM:
                    ofs << ": MGK Inform";
                    /////////////variable
                    break;
                case WLAN_SP_MGK_ACK:
                    ofs << ": MGK Acknowledgment";
                    /////////////variable
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_DMG: // DMG
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_WMM: // WMM
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_FST: // FST
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_UNPROT_DMG: // Unprotected DMG       
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_VHT: // VHT 802.11ac
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                case WLAN_VHT_ACTION_COMPRESSED_BF:
                    ofs << ": Compressed Beamforming";
                    break;
                case WLAN_VHT_ACTION_GROUPID_MGMT:
                    ofs << ": Group ID Management";
                    break;
                case WLAN_VHT_ACTION_OPMODE_NOTIF:
                    ofs << ": Operation Mode Notify"
                        << "\nOperating Mode:           "
                        << (unsigned)ie80211_un->ieee80211_mgmt.u.action.u.vht_opmode_notif.operating_mode;
                    break;
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_VENDOR_SPECIFIC_PROTECTED: // Vendor Specific Protected
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            case WLAN_CATEGORY_VENDOR_SPECIFIC: // Vendor Specific
                // Process Action Code
                switch((unsigned)ie80211_un->ieee80211_mgmt.u.action.u.addba_req.action_code) {
                default: // unknown action code, check online
                    ofs << ": Unknown Action Code";
                    break;
                };
                break;
            default: // unknown action category and action code, check online
                ofs << ": Unknown Action Code";    
                break;
            }; // MGMT Action Category Switch End
            break;
        default: // unknown subtype, check reserves online for others
            ofs << GetJustFSubType(ie80211_un) << ": Unknown Frame Subtype"
                << "\n                          "
                << GetFrameSubType(ie80211_un) << ": Unknown Frame + Subtype Total";
            break;
        }; // MGMT Frame Subtype Switch End
        break;
    // Control Frames
    case WIFI_CTRL_FRAME:
        // Print
        ofs << "1:  Control Frame";

        // Process Frame Subtype
        ofs << "\nFrame Subtype:            ";
        switch(GetFrameSubType(ie80211_un)) {
        case WIFI_PSPOLL:
            ofs << "10: Power Save Poll(PS-Poll)"
                << "\nAssociation ID:           " << le16toh(ie80211_un->ieee80211_pspoll.aid)               
                << "\nTransmitter Address:      "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_pspoll.ta, (char*)ta)
                << "\nBSSID:                    "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_pspoll.bssid, (char*)bssid);
            break;
        case WIFI_RTS:
            ofs << "11: Request To Send(RTS)"
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_rts.duration)               
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_rts.ra, (char*)ra)
                << "\nTransmitter Address:      "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_rts.ta, (char*)ta);
            break;
        case WIFI_CTS:
            ofs << "12: Clear To Send(CTS)"               
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_cts.duration)
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_cts.ra, (char*)ra);
            break;
        case WIFI_ACK:
            ofs << "13: Acknowledgment(ACK)"
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_ack.duration)               
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_ack.ra, (char*)ra);
            break;
        case WIFI_CFEND:
            ofs << "14: Contention Free End(CF-End)"
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_cfend.duration)
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_cfend.ra, (char*)ra);
            break;
        case WIFI_CFEND_CFACK:
            ofs << "15: CF-End + CF-Ack"
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_cfendack.duration)               
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_cfendack.ra, (char*)ra)
                << "\nTransmitter Address:      "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_cfendack.ta, (char*)ta);
            break;
        case WIFI_CTL_EXT: // Control Wrapper EXT (802.11n)
            ofs << "6:  Control Extension"
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_ctrlext.duration)               
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_ctrlext.ra, (char*)ra)
                << "\nCarried Frame Control:    " << le16toh(ie80211_un->ieee80211_ctrlext.carried_frame_ctrl)
                << "\nHT Control Field:         " << le16toh(ie80211_un->ieee80211_ctrlext.ht_ctrl)
                << "\nCarried Frame Follows:    ";
            break;
        case WIFI_BACK_REQ:
            ofs << "8:  Block Acknowledgment Request"
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_backreq.duration)               
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_backreq.ra, (char*)ra)
                << "\nTransmitter Address:      "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_backreq.ta, (char*)ta)
                << "\nBAR Control Total:        "
                << le16toh(ie80211_un->ieee80211_backreq.bar_ctrl)
                << "\nStart Sequence Control:   "
                << le16toh(ie80211_un->ieee80211_backreq.start_seq_ctrl);
            break;
        case WIFI_BACK:
            ofs << "9:  Block Acknowledgment"
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_back.duration)               
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_back.ra, (char*)ra)
                << "\nTransmitter Address:      "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_back.ta, (char*)ta)
                << "\nBAR Control Total:        "
                << le16toh(ie80211_un->ieee80211_back.bar_ctrl)
                << "\nStart Sequence Control:   "
                << le16toh(ie80211_un->ieee80211_back.start_seq_ctrl)
                << "\nBACK Bitmap:              "
                << le16toh(ie80211_un->ieee80211_back.bitmap);
            break;
        default: // unknown subtype, check reserves online for others, guessing on print below
            ofs << GetJustFSubType(ie80211_un) << ": Unknown Frame Subtype"
                << "\n                          "
                << GetFrameSubType(ie80211_un) << ": Unknown Frame + Subtype Total"
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_rts.duration)               
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_rts.ra, (char*)ra)
                << "\nTransmitter Address:      "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_rts.ta, (char*)ta);
            break;
        }; // CTRL Frame Subtype Switch End
        break;
    // Data Frames
    case WIFI_DATA_FRAME:
        ofs << "2:  DATA Frame";

        // Process Frame Subtype
        ofs << "\nFrame Subtype:            ";
        switch(GetFrameSubType(ie80211_un)) {
        case WIFI_DATA:
            ofs << "0:  Data";
            break;
        case WIFI_DATA_CFACK:
            ofs << "1:  Data, CF-Ack";
            break;
        case WIFI_DATA_CFPOLL:
            ofs << "2:  Data, CF-Poll";
            break;
        case WIFI_DATA_CFACKPOLL:
            ofs << "3:  Data, CF-Ack + CF-Poll";
            break;
        case WIFI_DATA_NULL:
            ofs << "4:  No Data";
            break;
        case WIFI_CFACK:
            ofs << "5:  No Data, CF-Ack";
            break;
        case WIFI_CFPOLL:
            ofs << "6:  No Data, CF-Poll";
            break;
        case WIFI_CFACKPOLL:
            ofs << "7:  No Data, CF-Ack + CF-Poll";
            break;
        case WIFI_QOS_DATA:
            ofs << "8:  QOS Data";
            qos = true;
            break;
        case WIFI_QOS_DATA_CFACK:
            ofs << "9:  QOS Data, CF-Ack";
            qos = true;
            break;
        case WIFI_QOS_DATA_CFPOLL:
            ofs << "10: QOS Data, CF-Poll";
            qos = true;
            break;
        case WIFI_QOS_DATA_CFACKPOLL:
            ofs << "11: QOS Data, CF-Ack + CF-Poll";
            qos = true;
            break;
        case WIFI_QOS_NULL:
            ofs << "12: QOS No Data";;
            qos = true;
            break;
        case WIFI_QOS_CFACK:
            ofs << "13: QOS No Data, CF-Ack";
            qos = true;
            break;
        case WIFI_QOS_CFPOLL:
            ofs << "14: QOS No Data, CF-Poll";
            qos = true;
            break;
        case WIFI_QOS_CFACKPOLL:
            ofs << "15: QOS No Data, CF-Ack + CF-Poll";
            qos = true;
            break;
        default: // unknown subtype, check reserves online for others
            ofs << GetJustFSubType(ie80211_un) << ": Unknown Frame Subtype"
                << "\n                          "
                << GetFrameSubType(ie80211_un) << ": Unknown Frame + Subtype Total";
            break;
        }; // Data Frame Subtype Switch End

        // Process Address Count
        if(addr_count_is_3)
            ofs << flow
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_3.duration_id)
                << saddr1 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_3.addr1, (char*)addr1)
                << saddr2 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_3.addr2, (char*)addr2)
                << saddr3 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_3.addr3, (char*)addr3)
                << "\nFragment Offset:          " << FRAG_NUM(ie80211_un->ieee80211_3.seq_ctrl)
                << "\nSequence Control:         " << SEQ_NUM(ie80211_un->ieee80211_3.seq_ctrl);
        else {
            ofs << flow
                << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_4.duration_id)
                << saddr1 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr1, (char*)addr1)
                << saddr2 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr2, (char*)addr2)
                << saddr3 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr3, (char*)addr3)
                << "\nFragment Offset:          " << FRAG_NUM(ie80211_un->ieee80211_4.seq_ctrl)               
                << "\nSequence Control:         " << SEQ_NUM(ie80211_un->ieee80211_4.seq_ctrl)
                << saddr4 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr4, (char*)addr4);
        }

        // Check QOS To Print QOS Control Field
        if(qos)
            ofs << "\nQOS Control:              " << le16toh(ie80211_un->ieee80211_qos_4.qos_ctrl);
        break;
    // Extension Frames, Guess On Some Print Below
    case WIFI_EXT_FRAME:
        ofs << "3: Extension Frame";

        // Process Frame Subtype
        ofs << "\nFrame Subtype:            ";
        switch(GetFrameSubType(ie80211_un)) {
        default: // unknown subtype, check reserves online for others
            ofs << GetJustFSubType(ie80211_un) << ": Unknown Frame Subtype"
                << "\n                          "
                << GetFrameSubType(ie80211_un) << ": Unknown Frame + Subtype Total";
        };

        // Process Address Count, Guessing On EXT
        if(len - sizeof(ieee80211_rts_hdr)) { // not null means header has more than 2 addrs
            if(addr_count_is_3)
                ofs << flow
                    << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_3.duration_id)
                    << saddr1 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_3.addr1, (char*)addr1)
                    << saddr2 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_3.addr2, (char*)addr2)
                    << saddr3 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_3.addr3, (char*)addr3)
                    << "\nFragment Offset:          " << FRAG_NUM(ie80211_un->ieee80211_3.seq_ctrl)
                    << "\nSequence Control:         " << SEQ_NUM(ie80211_un->ieee80211_3.seq_ctrl);
            else {
                ofs << flow
                    << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_4.duration_id)
                    << saddr1 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr1, (char*)addr1)
                    << saddr2 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr2, (char*)addr2)
                    << saddr3 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr3, (char*)addr3)
                    << "\nFragment Offset:          " << FRAG_NUM(ie80211_un->ieee80211_4.seq_ctrl)                   
                    << "\nSequence Control:         " << SEQ_NUM(ie80211_un->ieee80211_4.seq_ctrl)
                    << saddr4 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr4, (char*)addr4);
            }
        }
        else { // is null, 2 addrs
            ofs << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_rts.duration)               
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_rts.ra, (char*)ra)
                << "\nTransmitter Address:      "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_rts.ta, (char*)ta);
        }
        break;
    // Unknown Frames
    default: // unknown frame and frame subtype, check reserves online for others, guess below
        ofs << GetFrameType(ie80211_un)    << ": Unknown Frame"
            << "\nFrame Subtype:            "
            << GetJustFSubType(ie80211_un) << ": Unknown Frame Subtype"
            << "\n                          "
            << GetFrameSubType(ie80211_un) << ": Unknown Frame + Subtype Total";

        // Process Address Count, Guessing On Default
        if(len - sizeof(ieee80211_rts_hdr)) { // not null means header has more than 2 addrs
            if(addr_count_is_3)
                ofs << flow
                    << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_3.duration_id)
                    << saddr1 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_3.addr1, (char*)addr1)
                    << saddr2 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_3.addr2, (char*)addr2)
                    << saddr3 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_3.addr3, (char*)addr3)
                    << "\nFragment Offset:          " << FRAG_NUM(ie80211_un->ieee80211_3.seq_ctrl)
                    << "\nSequence Control:         " << SEQ_NUM(ie80211_un->ieee80211_3.seq_ctrl);
            else {
                ofs << flow
                    << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_4.duration_id)
                    << saddr1 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr1, (char*)addr1)
                    << saddr2 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr2, (char*)addr2)
                    << saddr3 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr3, (char*)addr3)
                    << "\nFragment Offset:          " << FRAG_NUM(ie80211_un->ieee80211_4.seq_ctrl)
                    << "\nSequence Control:         " << SEQ_NUM(ie80211_un->ieee80211_4.seq_ctrl)
                    << saddr4 << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_4.addr4, (char*)addr4);
            }
        }
        else { // is null, 2 addrs
            ofs << "\nDuration:                 " << le16toh(ie80211_un->ieee80211_rts.duration)               
                << "\nReceiver Address:         "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_rts.ra, (char*)ra)
                << "\nTransmitter Address:      "
                << ether_ntoa_r((ether_addr*)ie80211_un->ieee80211_rts.ta, (char*)ta);
        }
        break;
    }; // Frame Type Switch End

    // Check To Print HT Control Field (802.11n) Through Order Bit
    u32 hctrl = 0;
    if(GetOrder(ie80211_un)) {
        if(addr_count_is_3) {
            ofs << "\nHT Control Field Sum:     " << le32toh(ie80211_un->ieee80211_ht_3.ht_ctrl);
            hctrl = le32toh(ie80211_un->ieee80211_ht_3.ht_ctrl);
        }
        else {
            ofs << "\nHT Control Field Sum:     " << le32toh(ie80211_un->ieee80211_ht_4.ht_ctrl);
            hctrl = le32toh(ie80211_un->ieee80211_ht_4.ht_ctrl);
        }

        // Continue Printing HT Control Field
        ofs << "\nLink Adaptation Control:      "
            << "\nReserved Bit(1):          " <<  (hctrl & 0x00000001 ? '1' : '0')
            << "\nTraining Reqest(TRQ):     " <<  (hctrl & 0x00000002 ? '1' : '0')
            << "\nMAI:                      " << ((hctrl & 0x0000003C) >> 2)
            << (hctrl & 0x0000003C == 0x0000003C ? ": ASELI, MFB/ASELC Interpreted As ASELC"
              :                                    ": MCS Request(MRQ), MFB/ASELC Interpreted As MFB");

        // Check MAI To Print MRQ Information
        if((hctrl & 0x0000003C >> 2) != 14) {//////////////////////////////////////////////////////////////////////////////////////////////?
            ofs << "\nMCS Request(MRQ):          "
                << (hctrl & 0x00000040 ? "1: MCS Feedback" : "0: No MCS Feedback");

            // Check Feedback Bit Set For Sequence Or Reserved Fields Following
            if(hctrl & 0x00000040)
                ofs << "\nMRQ Sequence ID(MSI): " << ((hctrl & 0x00000038) >> 3);
            else
                ofs << "\nReserved Bits(4-6):   " << ((hctrl & 0x00000038) >> 3);
        }

        // Continue Printing HT Control Field
        ofs << "\nMFB Sequence ID(MFSI):    " << ((hctrl & 0x000001C0) >> 6)
            << "\nMFB/ASELC:                " << ((hctrl & 0x0000FE00) >> 8)
            << (((hctrl & 0x0000003C) >> 2) == 14  ? ": ASELC"
             :  ((hctrl & 0x0000FE00) >> 9) == 127 ? ": MFB: No MCS Feedback Present"
             :  ((hctrl & 0x0000FE00) >> 9) <  127 ? ": MFB: MCS Feedback Present"
             : ": Unknown"); ///////////////////////////////////////////////////////////////////////////////finish look in book for MFB and ASELC interp
            
        // Finish Printing HT Control Field
        ofs << "\nCalibration Position:     " << ((hctrl & 0x00030000) >> 16)
            << ((~hctrl & 0x00030000) == 0x00030000 ? ": Not A Calibration Frame"
             :    hctrl & 0x00030000  == 0x00030000 // must be before others cuz of multi bits
             ? ": Sounding Complete"
             :    hctrl & 0x00010000
             ? ": Calibration Start"
             :    hctrl & 0x00020000
             ? ": Sounding Response"
             : ": Unknown Calibration Position") // shouldn't happen
            << "\nCalibration Sequence:     " << ((hctrl & 0x000C0000) >> 18)
            << "\nReserved Bits(21-22):     " << ((hctrl & 0x00300000) >> 20)
            << "\nCSI/Steering:             " << ((hctrl & 0x00C00000) >> 22) 
            << ((~hctrl & 0x00C00000) == 0x00C00000
             ? ": No Feedback Required"
             :    hctrl & 0x00C00000  == 0x00C00000 // must be before other cuz of multi bits
             ? ": Compressed Beamforming"
             :    hctrl & 0x00400000
             ? ": CSI"
             :    hctrl & 0x00800000
             ? ": Noncompressed Beamforming"
             : ": Unknown CSI/Steering")
            << "\nNDP Announcement:         " <<  (hctrl & 0x01000000 ? '1' : '0')
            << "\nReserved Bits Sum(26-30): " << ((hctrl & 0x3E000000) >> 25)
            << "\nAC Constraint:            " <<  (hctrl & 0x40000000 ? '1' : '0')
            << "\nRDG/More PPDU:            " <<  (hctrl & 0x80400000 == 0x80400000 ? '1' : '0');
    }

    ofs << '\n';
    ofs.flush();
}

void Sniffer::printLSAP(unsigned char lsap) {
    // Defines
    #define LSAP (unsigned)lsap

    // Print LSAP Value
    ofs << (LSAP ==   0 ? "Null LSAP"
          : LSAP ==   2 ? "Individual LLC Sublayer Mgmt"
          : LSAP ==   3 ? "Group LLC Sublayer Mgmt"
          : LSAP ==   4 ? "SNA Path Control (individual)"
          : LSAP ==   5 ? "SNA Path Control (group)"
          : LSAP ==   6 ? "Reserved for DoD IP/ARPANET IP"
          : LSAP ==  14 ? "ProWay-LAN, Network Mgmt And Initialization"
          : LSAP ==  24 ? "Texas Instrument"
          : LSAP ==  66 ? "IEEE 802.1 Bridge Spanning Tree Protocol"
          : LSAP ==  78 ? "EIA-RS 511 Manufactoring Msg Service"
          : LSAP ==  94 ? "ISI IP"
          : LSAP == 126 ? "ISO 8208 (X.25 Over IEEE 802.2 Type LLC)"
          : LSAP == 128 ? "Xerox Network Systems(XNS)"
          : LSAP == 129 ? "BACnet/IP"
          : LSAP == 134 ? "Nestar"
          : LSAP == 142 ? "ProWay-LAN(IEC 955), Active Station List Maintenance"
          : LSAP == 152 ? "ARPANET Address Resolution Protocol(ARP)"
          : LSAP == 166 ? "Route Determination Entity(RDE)"
          : LSAP == 170 ? "SubNetwork Access Protocol Extension(SNAP)"
          : LSAP == 188 ? "Banyan Vines"                  
          : LSAP == 224 ? "Novell Netware"
          : LSAP == 240 ? "IBM NetBIOS"                  
          : LSAP == 244 ? "IBM LAN Management (individual)"  
          : LSAP == 245 ? "IBM LAN Management (group)"
          : LSAP == 248 ? "IBM Remote Program Load(RPL)"
          : LSAP == 250 ? "Ungermann-Bass"
          : LSAP == 254 ? "OSI Protocols ISO CLNS IS 8473"
          : LSAP == 255 ? "Global DSAP (cannot be used for SSAP)"
          :               "Unknown LSAP");

    // Undefines
    #undef LSAP
}

void Sniffer::printLLC(cuchar_cptr packet, c_uint len) {
    // Declarations
    const llc_hdr *llc = (llc_hdr*)packet;

    // Defines
    #define CTRL1 (unsigned)llc->ctrl1
    #define DSAP  (unsigned)llc->dsap
    #define SSAP  (unsigned)llc->ssap

    // Print LLC Header
    ofs << "\n~~~Logical Link Control 802.2 Header~~~"
        << "\nDest Service Access Point:    " << DSAP
        << "\nSrc  Service Access Point:    " << SSAP
        << "\nDSAP Cast:                    "
        << (CHECKBIT_LLC(&llc->dsap, 0) ? "Group Address"   : "Individual Address")
        << "\nSSAP Packet Type:             "
        << (CHECKBIT_LLC(&llc->ssap, 0) ? "Response Packet" : "Command Packet")
        << "\nD_Link Service Access Point:  ";
    printLSAP(llc->dsap);
    ofs << "\nS_Link Service Access Point:  ";
    printLSAP(llc->ssap);
    ofs << "\nLLC Control Type, 1st Octet:  " << CTRL1
        << (CTRL1 ==   0 ? ": Null SAP"
          : CTRL1 ==   3 ? ": Unnumbered Informatio(UI)"
          : CTRL1 == 170 ? ": SAP For SNAP"
          : CTRL1 == 175 ? ": Exchange Information(XID)"
          : CTRL1 == 191 ? ": Exchange Information(XID) Poll/Final"
          : CTRL1 == 227 ? ": TEST"
          : CTRL1 == 243 ? ": TEST Poll/Final"
          : CTRL1 == 255 ? ": Global SAP"
          :                ": Unknown Control Type")
        // add Info ctrl
        << "\nControl Type Poll/Final Flag: " << (CHECKBIT_LLC(&llc->ctrl1, 4) ? '1' : '0')
        << '\n';
    ofs.flush();

    // Undefines
    #undef CTRL1
    #undef DSAP
    #undef SSAP
}

void Sniffer::printSNAP(cuchar_cptr packet, c_uint len, c_bool eth_802_3) {
    // Declarations
    const snap_hdr *snap = (snap_hdr*)packet;
    char oui[OUI_PRINT_LEN];

    // Zero Out
    std::memset(oui, 0, OUI_LEN);

    std::snprintf(oui, OUI_PRINT_LEN, "%.2X:%.2X:%.2X", snap->oui[0], snap->oui[1], snap->oui[2]);

    // Print SNAP Header
    ofs << "\n~~~Subnetwork Access Protocol Header~~~"
        << "\nOUI:               " << oui
        << "\nOUI Name:          ";

    // Process OUI
    if((snap->oui[0] == oui_cisco[0]  &&
        snap->oui[1] == oui_cisco[1]  &&
        snap->oui[2] == oui_cisco[2]) ||
        snap->oui[0] == oui_cisco2[0] && 
        snap->oui[1] == oui_cisco2[1] && 
        snap->oui[2] == oui_cisco2[2])
        ofs << "Cisco Systems, Inc.";
    else if(snap->oui[0] == oui_apple[0] &&
            snap->oui[1] == oui_apple[1] &&
            snap->oui[2] == oui_apple[2])
        ofs << "Apple";
    else if(snap->oui[0] == oui_rfc1042[0] &&
            snap->oui[1] == oui_rfc1042[1] &&
            snap->oui[2] == oui_rfc1042[2])
        ofs << "Encapsulated Ethernet(rfc 1042)";
    else
        ofs << "Unknown OUI";

    if(eth_802_3)
        ofs << "\nLength:            " << ntohs(snap->ether_type);
    else {
        ofs << "\nEthernet Protocol: " << ntohs(snap->ether_type);
        printEtherType(ntohs(snap->ether_type));
    }
    
    ofs << '\n';
    ofs.flush();
}

void Sniffer::printEtherType(const __be16 h_proto) {
    // Defines
    #define EPRO h_proto
    
    // Print Ethernet Protocol Type
    ofs << (EPRO == ETH_P_LOOP       ? ": Ethernet Loopback Packet"
          : EPRO == ETH_P_PUP        ? ": Xerox PUP Packet"
          : EPRO == ETH_P_PUPAT      ? ": Xerox PUP Addr Trans Packet"
          : EPRO == ETH_P_IP         ? ": Internet Protocol Packet"
          : EPRO == ETH_P_X25        ? ": CCITT X.25"
          : EPRO == ETH_P_ARP        ? ": Address Resolution Packet"
          : EPRO == ETH_P_BPQ        ? ": G8BPQ AX.25 Ethernet Packet (Not Officially Registered)"
          : EPRO == ETH_P_IEEEPUP    ? ": Xerox IEEE802.3 PUP Packet"
          : EPRO == ETH_P_IEEEPUPAT  ? ": Xerox IEEE802.3 PUP Addr Trans Packet"
          : EPRO == ETH_P_BATMAN     ? ": B.A.T.M.A.N. - Advanced Packet (Not Officially Registered)"
          : EPRO == ETH_P_DEC        ? ": DEC Assigned Proto"
          : EPRO == ETH_P_DNA_DL     ? ": DEC DNA Dump/Load"
          : EPRO == ETH_P_DNA_RC     ? ": DEC DNA Remote Console"
          : EPRO == ETH_P_DNA_RT     ? ": DEC DNA Routing"
          : EPRO == ETH_P_LAT        ? ": DEC LAT"
          : EPRO == ETH_P_DIAG       ? ": DEC Diagnostics"
          : EPRO == ETH_P_CUST       ? ": DEC Customer Use"
          : EPRO == ETH_P_SCA        ? ": DEC Systems Comms Arch"
          : EPRO == ETH_P_TEB        ? ": Trans Ether Bridging"
          : EPRO == ETH_P_RARP       ? ": Reverse Addr Res Packet"
          : EPRO == ETH_P_ATALK      ? ": Appletalk DDP"
          : EPRO == ETH_P_AARP       ? ": Appletalk AARP"
          : EPRO == ETH_P_8021Q      ? ": 802.1Q VLAN Extended Header"
          : EPRO == ETH_P_IPX        ? ": IPX Over DIX"
          : EPRO == ETH_P_IPV6       ? ": IPv6 Over Bluebook"
          : EPRO == ETH_P_PAUSE      ? ": IEEE Pause Frames - See 802.3 31B"
          : EPRO == ETH_P_SLOW       ? ": Slow Protocol. See 802.3ad 43B"
          : EPRO == ETH_P_WCCP       ? ": Web-Cache Coordination Protocol"
          : EPRO == ETH_P_MPLS_UC    ? ": MPLS Unicast Traffic"
          : EPRO == ETH_P_MPLS_MC    ? ": MPLS Multicast Traffic"
          : EPRO == ETH_P_ATMMPOA    ? ": MultiProtocol Over ATM"
          : EPRO == ETH_P_PPP_DISC   ? ": PPPoE Discovery Messages" // PPPoE
          : EPRO == ETH_P_PPP_SES    ? ": PPPoE Session Messages"   // PPPoE
          : EPRO == ETH_P_LINK_CTL   ? ": HPNA, Wlan Link Local Tunnel"
          : EPRO == ETH_P_ATMFATE    ? ": Frame-Based ATM Transport - Over Ethernet"
          : EPRO == ETH_P_PAE        ? ": Port Access Entity (IEEE 802.1X)"
          : EPRO == ETH_P_AOE        ? ": ATA Over Ethernet"
          : EPRO == ETH_P_8021AD     ? ": 802.1ad Service VLAN"
          : EPRO == ETH_P_802_EX1    ? ": 802.1 Local Experimental 1"
          : EPRO == ETH_P_TIPC       ? ": TIPC"
          : EPRO == ETH_P_8021AH     ? ": 802.1ah Backbone Service Tag"
          : EPRO == ETH_P_MVRP       ? ": 802.1Q MVRP"
          : EPRO == ETH_P_1588       ? ": IEEE 1588 Timesync"
          : EPRO == ETH_P_PRP        ? ": IEC 62439-3 PRP/HSRv0"
          : EPRO == ETH_P_FCOE       ? ": Fibre Channel Over Ethernet"
          : EPRO == ETH_P_TDLS       ? ": TDLS"
          : EPRO == ETH_P_FIP        ? ": FCoE Initialization Protocol"
          : EPRO == ETH_P_80221      ? ": IEEE 802.21 Media Independent Handover Protocol"
          : EPRO == ETH_P_LOOPBACK   ? ": Ethernet Loopback Packet, Per IEEE 802.3"
          : EPRO == ETH_P_QINQ1      ? ": Deprecated QinQ VLAN (Not Officially Registered)"
          : EPRO == ETH_P_QINQ2      ? ": Deprecated QinQ VLAN (Not Officially Registered)"
          : EPRO == ETH_P_QINQ3      ? ": Deprecated QinQ VLAN (Not Officially Registered)"
          : EPRO == ETH_P_EDSA       ? ": Ethertype DSA (Not Officially Registered)"
          : EPRO == ETH_P_AF_IUCV    ? ": IBM af_iucv (Not Officially Registered)"
        //: EPRO == ETH_P_802_3_MIN  ? ": Ethernet II Before This, Else 802.3 After" // for comparison
          // Non DIX Types (Digital Equipment Corporation (DEC), Intel and Xerox)
          : EPRO == ETH_P_802_3      ? ": Dummy Type For 802.3 Frames"
          : EPRO == ETH_P_AX25       ? ": Dummy Protocol ID For AX.25"
          : EPRO == ETH_P_ALL        ? ": Every Packet"
          : EPRO == ETH_P_802_2      ? ": 802.2 Logical Link Layer Frame (LLC)" // LLC
          : EPRO == ETH_P_SNAP       ? ": SNAP - Internal Only"
          : EPRO == ETH_P_DDCMP      ? ": DEC DDCMP - Internal Only"
          : EPRO == ETH_P_WAN_PPP    ? ": Dummy Type For WAN PPP Frames" // PPP WAN
          : EPRO == ETH_P_PPP_MP     ? ": Dummy Type For PPP MP Frames"  // PPP MP
          : EPRO == ETH_P_LOCALTALK  ? ": Localtalk Pseudo Type"
          : EPRO == ETH_P_CAN        ? ": CAN: Controller Area Network"
          : EPRO == ETH_P_CANFD      ? ": CANFD: CAN Flexible Data Rate"
          : EPRO == ETH_P_PPPTALK    ? ": Dummy Type For Atalk Over PPP"
          : EPRO == ETH_P_TR_802_2   ? ": 802.2 TR Logical Link Layer Frame (LLC)" // LLC TR
          : EPRO == ETH_P_MOBITEX    ? ": Mobitex (kaz@cafe.net)"
          : EPRO == ETH_P_CONTROL    ? ": Card Specific Control Frames"
          : EPRO == ETH_P_IRDA       ? ": Linux-IrDA"
          : EPRO == ETH_P_ECONET     ? ": Acorn Econet"
          : EPRO == ETH_P_HDLC       ? ": HDLC Frames"
          : EPRO == ETH_P_ARCNET     ? ": 1A For ArcNet"
          : EPRO == ETH_P_DSA        ? ": Distributed Switch Arch"
          : EPRO == ETH_P_TRAILER    ? ": Trailer Switch Tagging"
          : EPRO == ETH_P_PHONET     ? ": Nokia Phonet Frames"
          : EPRO == ETH_P_IEEE802154 ? ": IEEE802.15.4 Frame"
          : EPRO == ETH_P_CAIF       ? ": ST-Ericsson CAIF Protocol"
          // Roofnet Added Experimentals
          : (EPRO == ETH_P_ROOFNET1 ||
             EPRO == ETH_P_ROOFNET3 ||
             EPRO == ETH_P_ROOFNET4 || 
             EPRO == ETH_P_ROOFNET5) ? ": Roofnet (Experimental)"
          // Cisco WDS OTAP And Aironet
          : EPRO == CISCO_OTAP_ETHER_TYPE    ? ": Cisco OTAP"
          : EPRO == CISCO_AIRONET_ETHER_TYPE ? ": Cisco Aironet"
          :                            ": Unknown Protocol");

    // Undefines
    #undef EPRO
}

void Sniffer::printEthernet(cuchar_cptr packet, c_uint len, c_bool eth_802_3) {
    // Declarations
    ethhdr *e = (ethhdr*)packet;
    unsigned char dst[ETH_PRINT_LEN], src[ETH_PRINT_LEN];
   
    // Zero Out
    std::memset(dst, 0, sizeof(dst));
    std::memset(src, 0, sizeof(src));

    // Format MAC Address
    std::snprintf((char*)dst, ETH_PRINT_LEN, "%.2X:%.2X:%.2X:%.2X:%.2X:%.2X",
        e->h_dest[0],   e->h_dest[1],   e->h_dest[2],   e->h_dest[3],   e->h_dest[4],   e->h_dest[5]);
    std::snprintf((char*)src, ETH_PRINT_LEN, "%.2X:%.2X:%.2X:%.2X:%.2X:%.2X",
        e->h_source[0], e->h_source[1], e->h_source[2], e->h_source[3], e->h_source[4], e->h_source[5]);
    
    // Print Ethernet Header
    ofs << "\n~~~Ethernet Header~~~"
        << "\nDestination MAC Address: " << dst
        << "\nSource MAC Address:      " << src;
    
    // Process Ethernet II/802.3 Header Type
    if(eth_802_3)
        ofs << "\nLength:                  " << ntohs(e->h_proto);
    else { // Ethernet II    
        ofs << "\nProtocol:                " << ntohs(e->h_proto);
        printEtherType(ntohs(e->h_proto));
    }

    ofs << '\n';
    ofs.flush();
}

void Sniffer::printIEEE8021X(cuchar_cptr packet, c_uint len) { // ETH_P_PAE, 802.1X
    // Declarations
    EAP_hdr *eap = (EAP_hdr*)packet;

    // Defines
    #define ECODE (unsigned)eap->code

    // Print EAP Header
    ofs << "\n~~~EAP, PAE 802.1X Header~~~"
        << "\nCode:   " << ECODE
        << (ECODE == 1 ? ": Request"
          : ECODE == 2 ? ": Response"
          : ECODE == 3 ? ": Success"
          : ECODE == 4 ? ": Failure"
          : ECODE == 5 ? ": Initiate"
          : ECODE == 6 ? ": Finish"
          :              ": Unknown Code")
        << "\nID:     " << (unsigned)eap->eapid
        << "\nLength: " << (unsigned)eap->length
        << '\n';
    ofs.flush();

    // Undefines
    #undef ECODE
}

void Sniffer::printARP_HAType(const __be16 ar_hrd) {
    // Defines
    #define ARPH ar_hrd
    
    // Print ARP Hardware Type
    ofs << (ARPH == ARPHRD_NETROM             ? ": From KA9Q: NET/ROM Pseudo"
          : ARPH == ARPHRD_ETHER              ? ": Ethernet 10Mbps"
          : ARPH == ARPHRD_EETHER             ? ": Experimental Ethernet"
          : ARPH == ARPHRD_AX25               ? ": AX.25 Level 2"
          : ARPH == ARPHRD_PRONET             ? ": PROnet Token Ring"
          : ARPH == ARPHRD_CHAOS              ? ": Chaosnet"
          : ARPH == ARPHRD_IEEE802            ? ": IEEE 802.2 Ethernet/TR/TB" // LLC TR/TB
          : ARPH == ARPHRD_ARCNET             ? ": ARCnet"
          : ARPH == ARPHRD_APPLETLK           ? ": APPLEtalk"
          : ARPH == ARPHRD_DLCI               ? ": Frame Relay DLCI"
          : ARPH == ARPHRD_ATM                ? ": ATM"
          : ARPH == ARPHRD_METRICOM           ? ": Metricom STRIP (New IANA ID)"
          : ARPH == ARPHRD_IEEE1394           ? ": IEEE 1394 IPv4"
          : ARPH == ARPHRD_EUI64              ? ": EUI-64"
          : ARPH == ARPHRD_INFINIBAND         ? ": InfiniBand"
          // Dummy Types (non-ARP Hardware)
          : ARPH == ARPHRD_SLIP               ? ": Serial Line IPv4"
          : ARPH == ARPHRD_CSLIP              ? ": Compressed Serial Line IPv4"
          : ARPH == ARPHRD_SLIP6              ? ": Serial Line IPv6"
          : ARPH == ARPHRD_CSLIP6             ? ": Compressed Serial Line IPv6"
          : ARPH == ARPHRD_RSRVD              ? ": Notional KISS Type"
          : ARPH == ARPHRD_ADAPT              ? ": A Dynamically Adaptive Protocol For Transmission"
          : ARPH == ARPHRD_ROSE               ? ": Remote Operations Service Element" 
          : ARPH == ARPHRD_X25                ? ": CCITT X.25"
          : ARPH == ARPHRD_HWX25              ? ": Boards With X.25 In Firmware"
          : ARPH == ARPHRD_CAN                ? ": Controller Area Network"
          : ARPH == ARPHRD_PPP                ? ": Point-to-Point Protocol" // PPP
          : ARPH == ARPHRD_CISCO              ? ": Cisco HDLC"
          : ARPH == ARPHRD_HDLC               ? ": Cisco HDLC"
          : ARPH == ARPHRD_LAPB               ? ": LAPB"
          : ARPH == ARPHRD_DDCMP              ? ": Digital's DDCMP Protocol"
          : ARPH == ARPHRD_RAWHDLC            ? ": Raw HDLC"
          : ARPH == ARPHRD_TUNNEL             ? ": PIP Tunnel"
          : ARPH == ARPHRD_TUNNEL6            ? ": IP6IP6 Tunnel"
          : ARPH == ARPHRD_FRAD               ? ": Frame Relay Access Device"
          : ARPH == ARPHRD_SKIP               ? ": SKIP vif"
          : ARPH == ARPHRD_LOOPBACK           ? ": Loopback Device"
          : ARPH == ARPHRD_LOCALTLK           ? ": Localtalk Device"
          : ARPH == ARPHRD_FDDI               ? ": Fiber Distributed Data Interface"
          : ARPH == ARPHRD_BIF                ? ": AP1000 BIF"
          : ARPH == ARPHRD_SIT                ? ": sit0 device - IPv6-in-IPv4"
          : ARPH == ARPHRD_IPDDP              ? ": IP Over DDP Tunneller"
          : ARPH == ARPHRD_IPGRE              ? ": GRE Over IP"
          : ARPH == ARPHRD_PIMREG             ? ": PIMSM Register Interface"
          : ARPH == ARPHRD_HIPPI              ? ": High Performance Parallel Interface"
          : ARPH == ARPHRD_ASH                ? ": Nexus 64Mbps Ash"
          : ARPH == ARPHRD_ECONET             ? ": Acorn Econet"
          : ARPH == ARPHRD_IRDA               ? ": Linux-IrDA"
          // ARP Works Different Over Fibrechannel
          : ARPH == ARPHRD_FCPP               ? ": Point-to-Point Fibrechannel" // FC PPP
          : ARPH == ARPHRD_FCAL               ? ": Fibrechannel Arbitrated Loop"
          : ARPH == ARPHRD_FCPL               ? ": Fibrechannel Public Loop"
          : ARPH == ARPHRD_FCFABRIC           ? ": Fibrechannel Fabric"
          : ARPH == ARPHRD_IEEE802_TR         ? ": Magic Type Ident For TR"
          : ARPH == ARPHRD_IEEE80211          ? ": IEEE 802.11"
          : ARPH == ARPHRD_IEEE80211_PRISM    ? ": IEEE 802.11 + Prism2 Header"
          : ARPH == ARPHRD_IEEE80211_RADIOTAP ? ": IEEE 802.11 + Radiotap Header"
          : ARPH == ARPHRD_IEEE802154         ? ": IEEE 802.15.4"
          : ARPH == ARPHRD_IEEE802154_MONITOR ? ": IEEE 802.15.4 Network Monitor"
          : ARPH == ARPHRD_PHONET             ? ": PhoNet Media Type"
          : ARPH == ARPHRD_PHONET_PIPE        ? ": PhoNet Pipe Header"
          : ARPH == ARPHRD_CAIF               ? ": CAIF Media Type"
          : ARPH == ARPHRD_IP6GRE             ? ": GRE Over IPv6"
          : ARPH == ARPHRD_NETLINK            ? ": Netlink Header"
          : ARPH == ARPHRD_6LOWPAN            ? ": IPv6 Over LoWPAN"
          : ARPH == ARPHRD_VOID               ? ": Void Type (Nothing Known)"
          : ARPH == ARPHRD_NONE               ? ": Zero Length Header (None)"
          :                                     ": Unknown Hardware Address");

    // Undefines
    #undef ARPH
}

void Sniffer::printARP(cuchar_cptr packet, c_uint len) {
    // Declarations
    const arphdr2 *arp = (arphdr2*)packet;
    unsigned char saddr[ETH_PRINT_LEN], taddr[ETH_PRINT_LEN], sipaddr[IP_PRINT_LEN], tipaddr[IP_PRINT_LEN];
    
    // Zero Out
    std::memset(saddr,   0, sizeof(saddr));
    std::memset(taddr,   0, sizeof(taddr));
    std::memset(sipaddr, 0, sizeof(sipaddr));
    std::memset(tipaddr, 0, sizeof(tipaddr));

    // Defines
    #define ARPO ntohs(arp->ar_op)
    
    // Format IP Address
    std::snprintf((char*)sipaddr, IP_PRINT_LEN, "%d.%d.%d.%d", arp->ar_sip[0], arp->ar_sip[1], arp->ar_sip[2], arp->ar_sip[3]);
    std::snprintf((char*)tipaddr, IP_PRINT_LEN, "%d.%d.%d.%d", arp->ar_tip[0], arp->ar_tip[1], arp->ar_tip[2], arp->ar_tip[3]);
    
    // Print ARP Header
    ofs << "\n~~~ARP Header~~~"
        << "\nHardware Address:        " << ntohs(arp->ar_hrd);
    printARP_HAType(ntohs(arp->ar_hrd));
    ofs << "\nProtocol:                " << ntohs(arp->ar_pro);
    printEtherType(ntohs(arp->ar_pro));
    ofs << "\nHardware Address Length: " << (unsigned)arp->ar_hln
        << "\nProtocol Address Length: " << (unsigned)arp->ar_pln
        << "\nARP Opcode(command):     " << ntohs(arp->ar_op)
        << (ARPO == ARPOP_REQUEST   ? ": ARP Request"
          : ARPO == ARPOP_REPLY     ? ": ARP Reply"
          : ARPO == ARPOP_RREQUEST  ? ": RARP Request"
          : ARPO == ARPOP_RREPLY    ? ": RARP Reply"
          : ARPO == ARPOP_InREQUEST ? ": InARP Request"
          : ARPO == ARPOP_InREPLY   ? ": InARP Reply"
          : ARPO == ARPOP_NAK       ? ": (ATM)ARP NAK"
          :                           ": Unknown Opcode")
        << "\nSender Hardware Address: " << ether_ntoa_r((ether_addr*)arp->ar_sha, (char*)saddr) // need reentrants
        << "\nSender IP Address:       " << sipaddr
        << "\nTarget Hardware Address: " << ether_ntoa_r((ether_addr*)arp->ar_tha, (char*)taddr)
        << "\nTarget IP Address:       " << tipaddr
        << '\n';
    ofs.flush();

    // Undefines
    #undef ARPO
}

void Sniffer::printIP_Proto(const char protocol) {
    // Defines
    #define IPPRO (unsigned)protocol

    // Print IP Protocol
    ofs << (IPPRO == IPPROTO_IP      ? ": Dummy Protocol For TCP"
          : IPPRO == IPPROTO_ICMP    ? ": Internet Control Message Protocol"
          : IPPRO == IPPROTO_IGMP    ? ": Internet Group Management Protocol"
          : IPPRO == IPPROTO_IPIP    ? ": IPIP Tunnels"
          : IPPRO == IPPROTO_TCP     ? ": Transmission Control Protocol"
          : IPPRO == IPPROTO_EGP     ? ": Exterior Gateway Protocol"
          : IPPRO == IPPROTO_PUP     ? ": PUP Protocol"
          : IPPRO == IPPROTO_UDP     ? ": User Datagram Protocol"
          : IPPRO == IPPROTO_IDP     ? ": XNS IDP Protocol"
          : IPPRO == IPPROTO_TP      ? ": SO Transport Protocol Class 4"
          : IPPRO == IPPROTO_DCCP    ? ": Datagram Congestion Control Protocol"
          : IPPRO == IPPROTO_IPV6    ? ": IPv6-In-IPv4 Tunnelling"
          : IPPRO == IPPROTO_RSVP    ? ": RSVP Protocol"
          : IPPRO == IPPROTO_GRE     ? ": Cisco GRE Tunnels"
          : IPPRO == IPPROTO_ESP     ? ": Encapsulation Security Payload Protocol"
          : IPPRO == IPPROTO_AH      ? ": Authentication Header Protocol"
          : IPPRO == IPPROTO_MTP     ? ": Multicast Transport Protocol"
          : IPPRO == IPPROTO_BEETPH  ? ": IP Option Pseudo Header For BEET/Older KA9Q Tunnels"
          : IPPRO == IPPROTO_ENCAP   ? ": Encapsulation Header"
          : IPPRO == IPPROTO_PIM     ? ": Protocol Independent Multicast"
          : IPPRO == IPPROTO_COMP    ? ": Compression Header Protocol"
          : IPPRO == IPPROTO_SCTP    ? ": Stream Control Transport Protocol"
          : IPPRO == IPPROTO_UDPLITE ? ": UDP-Lite"
          : IPPRO == IPPROTO_RAW     ? ": Raw IP packets"
          :                            ": Unknown Protocol");

    // Undefines
    #undef IPPRO
}

void Sniffer::printIP(cuchar_cptr packet, c_uint len) {
    // Declarations
    const iphdr   *ip4 = (iphdr*)  packet;
    const ipv6hdr *ip6 = (ipv6hdr*)packet;
    sockaddr_in    src4, dst4;
    sockaddr_in6   src6, dst6;
    unsigned char  ssin4[IP_PRINT_LEN],   dsin4[IP_PRINT_LEN],
                   ssin6[IP_PRINT_LEN_6], dsin6[IP_PRINT_LEN_6],
                   oui[OUI_LEN], flow_lbl[IPV6_FLOW_LBL_LEN];

    // Defines
    #define IPTOS (unsigned)ip4->tos

    // Zero Out IP Addresses
    std::memset(ssin4,    0, IP_PRINT_LEN);
    std::memset(dsin4,    0, IP_PRINT_LEN);
    std::memset(ssin6,    0, IP_PRINT_LEN_6);
    std::memset(dsin6,    0, IP_PRINT_LEN_6);
    std::memset(&src4,    0, sizeof(sockaddr_in));
    std::memset(&dst4,    0, sizeof(sockaddr_in));
    std::memset(&src6,    0, sizeof(sockaddr_in6));
    std::memset(&dst6,    0, sizeof(sockaddr_in6));   
    std::memset(oui,      0, OUI_LEN);
    std::memset(flow_lbl, 0, IPV6_FLOW_LBL_LEN);   
    
    // Fill Socket Addresses And IPV6 Flow Label
    src4.sin_addr.s_addr = ip4->saddr;
    dst4.sin_addr.s_addr = ip4->daddr;
    src6.sin6_addr       = ip6->saddr;
    dst6.sin6_addr       = ip6->daddr;
    std::snprintf((char*)flow_lbl, IPV6_FLOW_LBL_PRINT_LEN, "%.2X:%.2X:%.2X",
                  ip6->flow_lbl[0], ip6->flow_lbl[1], ip6->flow_lbl[2]);

    // Process IP Version And Print
    ofs << "\n~~~IP Header~~~"
        << "\nVersion:                 " << (unsigned)ip4->version;
    if((unsigned)ip4->version == IPV4) { // IPv4
        ofs << ": IPv4"
            << "\nHeader Length:           " << (unsigned)ip4->ihl
            << "\nType of Service:         " << IPTOS
            << (IPTOS == IPTOS_LOWDELAY             ? ": Low Delay"
              : IPTOS == IPTOS_THROUGHPUT           ? ": Throughput"
              : IPTOS == IPTOS_RELIABILITY          ? ": Reliability"
              : IPTOS == IPTOS_MINCOST              ? ": Minimum Cost"
              : IPTOS == IPTOS_PREC_NETCONTROL      ? ": Precedence - NETControl"
              : IPTOS == IPTOS_PREC_INTERNETCONTROL ? ": Precedence - Internet Control"
              : IPTOS == IPTOS_PREC_CRITIC_ECP      ? ": Precedence - Critical And Emergency Call Processing"
              : IPTOS == IPTOS_PREC_FLASHOVERRIDE   ? ": Precedence - Flash Overide"
              : IPTOS == IPTOS_PREC_FLASH           ? ": Precedence - Flash"
              : IPTOS == IPTOS_PREC_IMMEDIATE       ? ": Precedence - Immediate"
              : IPTOS == IPTOS_PREC_PRIORITY        ? ": Precedence - Priority"
              : IPTOS == IPTOS_PREC_ROUTINE         ? ": Precedence - Routine"
              :                                       ": Unknown Type Of Service")
            << "\nTotal Length:            " << ntohs(ip4->tot_len)
            << "\nID:                      " << ntohs(ip4->id)
            << "\nFragment Offset:         " << ntohs(ip4->frag_off)
            << "\nReserved 0 Field:        " << (CHECKBIT_IP(&ip4->frag_off, 0) ? '1' : '0')
            << "\nDont Fragment Field:     " << (CHECKBIT_IP(&ip4->frag_off, 1) ? '1' : '0')
            << "\nMore Fragment Field:     " << (CHECKBIT_IP(&ip4->frag_off, 2) ? '1' : '0')
            << "\nTime-To-Live:            " << (unsigned)ip4->ttl << " hops(secs)"
            << "\nProtocol:                " << (unsigned)ip4->protocol;
        printIP_Proto(ip4->protocol);
        ofs << "\nSource Address:          "
            << inet_ntop(AF_INET, (const void*)&(((sockaddr_in*)&src4)->sin_addr), (char*)ssin4, IP_PRINT_LEN)
            << "\nDestination Address:     "
            << inet_ntop(AF_INET, (const void*)&(((sockaddr_in*)&dst4)->sin_addr), (char*)dsin4, IP_PRINT_LEN)
            << "\nChecksum:                " << ntohs(ip4->check);
    }
    else if((unsigned)ip4->version == IPV6) { // IPv6
        ofs << ": IPv6"
            << "\nPriority(Traffic Class): " << (unsigned)ip6->priority
            << "\nFlow Label:              " << flow_lbl//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////mite be wrong in printing due to it being array
            << "\nIPv6 Payload Length:     " << ntohs(ip6->payload_len) // add data following IPv6 header
            << "\nNext Header(Protocol):   " << (unsigned)ip6->nexthdr;
        printIP_Proto(ip6->nexthdr);
        ofs << "\nHop Limit:               " << (unsigned)ip6->hop_limit
            << "\nSource Address:          "
            << inet_ntop(AF_INET6, (const void*)&(((sockaddr_in6*)&src6)->sin6_addr), (char*)ssin6, IP_PRINT_LEN_6)
            << "\nDestination Address:     "
            << inet_ntop(AF_INET6, (const void*)&(((sockaddr_in6*)&dst6)->sin6_addr), (char*)dsin6, IP_PRINT_LEN_6);
    }
    else // IPv?
        ofs << ": Unknown IP Version";
   
    ofs << '\n';
    ofs.flush();

    // Undefines
    #undef IPTOS
}

void Sniffer::printTCP(cuchar_cptr packet, c_uint len) {
    // Declarations
    const tcphdr *tcp = (tcphdr*)packet;
    
    // Print TCP Header
    ofs << "\n~~~TCP Header~~~"
        << "\nSource Port:      " << ntohs(tcp->source)
        << "\nDestination Port: " << ntohs(tcp->dest)
        << "\nSequence Num:     " << ntohl(tcp->seq)
        << "\nAcknowledge Num:  " << ntohl(tcp->ack_seq)
        << "\nHeader Length:    " << (unsigned)tcp->doff
        << "\nReserved Flag:    " << (unsigned)tcp->res1
      //<< "\nExplicit Congestion Notification Flag: " << (unsigned)tcp->ece
      //<< "\nCongestion Window Reduced Flag:        " << (unsigned)tsp->cwr
        << "\nUrgent Flag:      " << (unsigned)tcp->urg
        << "\nAcknowledge Flag: " << (unsigned)tcp->ack
        << "\nPush Flag:        " << (unsigned)tcp->psh
        << "\nReset Flag:       " << (unsigned)tcp->rst
        << "\nSynchronise Flag: " << (unsigned)tcp->syn
        << "\nFinish Flag:      " << (unsigned)tcp->fin
        << "\nWindow:           " << ntohs(tcp->window)
        << "\nChecksum:         " << ntohs(tcp->check)
        << "\nUrgent Pointer:   " << ntohs(tcp->urg_ptr)
        << '\n';
    ofs.flush();
}

void Sniffer::printUDP(cuchar_cptr packet, c_uint len) {
    // Declarations
    const udphdr *udp = (udphdr*)packet;
    std::cout << ntohs(udp->source);
    // Print UDP Header
    ofs << "\n~~~UDP Header~~~"
        << "\nSource Port:      " << ntohs(udp->source)
        << "\nDestination Port: " << ntohs(udp->dest)
        << "\nHeader Length:    " << ntohs(udp->len)
        << "\nChecksum:         " << ntohs(udp->check)
        << '\n';
    ofs.flush();
}

void Sniffer::printSCTP(cuchar_cptr packet, c_uint len) {
    // Declarations
    const sctphdr2       *sctp  = (sctphdr2*)packet;
    const sctp_chunkhdr2 *sctpC = (sctp_chunkhdr2*)((cuchar_cptr)sctp + sizeof(sctp_chunkhdr2));

    // Print SCTP Header And Chunck Data
    ofs << "\n~~~SCTP Header~~~"
        << "\nSource Port:      " << ntohs(sctp->source)
        << "\nDestination Port: " << ntohs(sctp->dest)
        << "\nVerification Tag: " << ntohl(sctp->vtag)
        << "\nChecksum:         " << ntohs(sctp->checksum)
        << "\n\n~~~SCTP Chunk~~~"
        << "\nType:             " << (unsigned)sctpC->type
        << "\nFlags:            " << (unsigned)sctpC->flags
        << "\nLength:           " << ntohs(sctpC->length)
        << '\n';
    ofs.flush();
}

void Sniffer::printICMP(cuchar_cptr packet, c_uint len) {
    // Declarations
    const icmphdr *icmp = (icmphdr*)packet;
    unsigned char gatekeeper[ETH_PRINT_LEN]; // gateway address

    // Zero Out
    std::memset(gatekeeper, 0, sizeof(gatekeeper));

    // Defines
    #define ICMPT (unsigned)icmp->type
    #define ICMPC (unsigned)icmp->code

    // Print ICMP Header
    ofs << "\n~~~ICMP Header~~~"
        << "\nType:                   " << ICMPT
        << (ICMPT == ICMP_ECHOREPLY      ? ": Echo Reply"
          : ICMPT == ICMP_DEST_UNREACH   ? ": Destination Unreachable"
          : ICMPT == ICMP_SOURCE_QUENCH  ? ": Source Quench (Deprecated)"
          : ICMPT == ICMP_REDIRECT       ? ": Redirect - Change Route"
          : ICMPT == ICMP_ECHO           ? ": Echo Request"
          : ICMPT == ICMP_TIME_EXCEEDED  ? ": Time Exceeded"
          : ICMPT == ICMP_PARAMETERPROB  ? ": Parameter Problem"
          : ICMPT == 9                   ? ": Router Advertisement"
          : ICMPT == 10                  ? ": Router Solicitation"
          : ICMPT == ICMP_TIMESTAMP      ? ": Timestamp Request"
          : ICMPT == ICMP_TIMESTAMPREPLY ? ": Timestamp Reply"
          : ICMPT == ICMP_INFO_REQUEST   ? ": Information Request (Deprecated)"
          : ICMPT == ICMP_INFO_REPLY     ? ": Information Reply (Deprecated)"
          : ICMPT == ICMP_ADDRESS        ? ": Address Mask Request (Deprecated)"
          : ICMPT == ICMP_ADDRESSREPLY   ? ": Address Mask Reply (Deprecated)"
          : ICMPT == 30                  ? ": Traceroute (Deprecated)"
          :                                ": Destination Unreachable, Unknown Type")
        << "\nCode:                   " << ICMPC;
    if(ICMPT == ICMP_DEST_UNREACH)
        ofs << (ICMPC == ICMP_NET_UNREACH    ? ": Network Unreachable (Gateway)"
              : ICMPC == ICMP_HOST_UNREACH   ? ": Host Unreachable (Gateway)"
              : ICMPC == ICMP_PROT_UNREACH   ? ": Protocol Unreachable (Host)"
              : ICMPC == ICMP_PORT_UNREACH   ? ": Port Unreachable (Host)"
              : ICMPC == ICMP_FRAG_NEEDED    ? ": Fragmentation Needed/DF Set (Gateway)"
              : ICMPC == ICMP_SR_FAILED      ? ": Source Route Failed (Gateway)"
              : ICMPC == ICMP_NET_UNKNOWN    ? ": Destination Network Unknown (Gateway)"
              : ICMPC == ICMP_HOST_UNKNOWN   ? ": Destination Host Unknown (Host)"
              : ICMPC == ICMP_HOST_ISOLATED  ? ": Source Host Isolated (Host)"
              : ICMPC == ICMP_NET_ANO        ? ": Destination Network Prohibited (Gateway)"
              : ICMPC == ICMP_HOST_ANO       ? ": Destination Host Prohibited (Host)"
              : ICMPC == ICMP_NET_UNR_TOS    ? ": Destination Network Unreachable For Type Of Service (Gateway)"
              : ICMPC == ICMP_HOST_UNR_TOS   ? ": Destination Host Unreachable For Type Of Service (Host)"
              : ICMPC == ICMP_PKT_FILTERED   ? ": Communication Prohibited - Packet Filtered (Gateway)"
              : ICMPC == ICMP_PREC_VIOLATION ? ": Precedence Violation (Gateway)"
              : ICMPC == ICMP_PREC_CUTOFF    ? ": Precedence Cutoff (Gateway)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == 9)
        ofs << (ICMPC == 0                   ? ": Router Advertisement (Gateway)"
              : ICMPC == 16                  ? ": No Routeing Common Traffic (Gateway)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == 10)
        ofs << (ICMPC == 0                   ? ": Router Discovery/Selection/Solicitation (Gateway)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == ICMP_TIME_EXCEEDED)
        ofs << (ICMPC == ICMP_EXC_TTL        ? ": Time To Live Count Exceeded (Gateway)"
              : ICMPC == ICMP_EXC_FRAGTIME   ? ": Fragment Reassembley Time Exceeded (Host)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == ICMP_PARAMETERPROB)
        ofs << (ICMPC == 0                   ? ": Pointer Indicates The Error In Specified Octet (Gateway Or Host)"
              : ICMPC == 1                   ? ": Missing A Required Option (Gateway Or Host)"
              : ICMPC == 2                   ? ": Bad Length (Gateway Or Host)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == ICMP_SOURCE_QUENCH)
        ofs << (ICMPC == 0                   ? ": Source Quench Message (Gateway Or Host) (Deprecated)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == ICMP_REDIRECT)
        ofs << (ICMPC == ICMP_REDIR_NET      ? ": Redirect Datagrams For Network (Gateway)"
              : ICMPC == ICMP_REDIR_HOST     ? ": Redirect Datagrams For Host (Gateway)"
              : ICMPC == ICMP_REDIR_NETTOS   ? ": Redirect Datagrams For Network And Type Of Service (Gateway)"
              : ICMPC == ICMP_REDIR_HOSTTOS  ? ": Redirect Datagrams For Host And Type Of Service (Gateway)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == ICMP_ECHO         || ICMPT == ICMP_ECHOREPLY)
        ofs << (ICMPC == 0                   ? ": Identifier Or Sequence Number May Be Zero (Gateway Or Host)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == ICMP_TIMESTAMP    || ICMPT == ICMP_TIMESTAMPREPLY)
        ofs << (ICMPC == 0                   ? ": Identifier Or Sequence Number May Be Zero (Gateway Or Host)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == ICMP_INFO_REQUEST || ICMPT == ICMP_INFO_REPLY)
        ofs << (ICMPC == 0                   ? ": Identifier Or Sequence Number May Be Zero (Gateway Or Host)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == ICMP_ADDRESS      || ICMPT == ICMP_ADDRESSREPLY)
        ofs << (ICMPC == 0                   ? ": Identifier Or Sequence Number May Be Zero (Gateway Or Host) (Deprecated)"
              :                                ": Destination Unreachable, Unknown Code");
    else if(ICMPT == 30)
        ofs << (ICMPC == 0                   ? ": Information Request (Gateway) (Deprecated)"
              :                                ": Destination Unreachable, Unknown Code");
    ofs << "\nChecksum:               " << ntohs(icmp->checksum)
        << "\nID:                     " << ntohs(icmp->un.echo.id)
        << "\nSequence:               " << ntohs(icmp->un.echo.sequence)
        << "\nGateway:                " << ether_ntoa_r((ether_addr*)&icmp->un.gateway, (char*)gatekeeper) // need reentrant
        << "\nMaximum Transport Unit: " << ntohs(icmp->un.frag.mtu)
        << '\n';
    ofs.flush();

    // Undefines
    #undef ICMPT
    #undef ICMPC
}

void Sniffer::printIGMP(cuchar_cptr packet, c_uint len) {
    // Declarations
    const igmphdr *igmp = (igmphdr*)packet;
    unsigned char group_addr[ETH_PRINT_LEN]; // group address

    // Zero Out
    std::memset(group_addr, 0, sizeof(group_addr));

    // Defines
    #define IGMPT (unsigned)igmp->type
    #define IGMPC (unsigned)igmp->code

    // Print IGMP Header
    ofs << "\n~~~IGMP Header~~~"
        << "\nType:     " << IGMPT
        << (IGMPT == IGMP_HOST_MEMBERSHIP_QUERY    ? ": Host Membership Query"
          : IGMPT == IGMP_HOST_MEMBERSHIP_REPORT   ? ": V1 Host Membership Report"
          : IGMPT == IGMP_DVMRP                    ? ": Distance Vector Multicast Routing Protocol"
          : IGMPT == IGMP_PIM                      ? ": Protocol-Independent Multicast"
          : IGMPT == IGMP_TRACE                    ? ": Cicso Trace Messages"
          : IGMPT == IGMPV2_HOST_MEMBERSHIP_REPORT ? ": V2 Host Membership Report"
          : IGMPT == IGMP_HOST_LEAVE_MESSAGE       ? ": V2 Host Leave Message Group"
          : IGMPT == IGMPV3_HOST_MEMBERSHIP_REPORT ? ": V3 Host Membership Report"
          : IGMPT == IGMP_MTRACE_RESP              ? ": Multicast Traceroute Response"
          : IGMPT == IGMP_MTRACE                   ? ": Multicast Traceroute"
          : IGMPT == 0x30                          ? ": Multicast Router Advertisement"
          : IGMPT == 0x31                          ? ": Multicast Router Solicitation"
          : IGMPT == 0x32                          ? ": Multicast Router Termination"
          :                                          ": Unknown Type")
        << "\nCode:     " << IGMPC;
    
        // Need for -Wextra Since Comparison Is Always True Due To Limited Range Of Data Type
        unsigned u = 255;

        // Print Correct Code Given Type
        if(IGMPT == IGMP_HOST_MEMBERSHIP_QUERY)
            ofs <<  (IGMPC == 0 ? ": IGMP V1"
                  :  IGMPC >= 1
                  && IGMPC <= u ? ": IGMP V2 Or Above Max Response Time"
                  :               ": Unknown Code");
        else if(IGMPT == IGMP_DVMRP)
            ofs << (IGMPC == 1  ? ": Probe" 
                  : IGMPC == 2  ? ": Route Report"
                  : IGMPC == 3  ? ": Old Ask Neighbors"
                  : IGMPC == 4  ? ": Old Neighbors Reply"
                  : IGMPC == 5  ? ": Ask Neighbors"
                  : IGMPC == 6  ? ": Neighbors Reply"
                  : IGMPC == 7  ? ": Prune"
                  : IGMPC == 8  ? ": Graft"
                  : IGMPC == 9  ? ": Graft Ack"
                  :               ": Unknown Code");
        else if(IGMPT == IGMP_PIM)
            ofs << (IGMPC == 0  ? ": Query"
                  : IGMPC == 1  ? ": Register"
                  : IGMPC == 2  ? ": Register-Stop"
                  : IGMPC == 3  ? ": Join/Prune"
                  : IGMPC == 4  ? ": RP-Reachable"
                  : IGMPC == 5  ? ": Assert"
                  : IGMPC == 6  ? ": Graft"
                  : IGMPC == 7  ? ": Graft Ack"
                  : IGMPC == 8  ? ": Mode"
                  :               ": Unknown Code");

    ofs << "\nChecksum: " << ntohs(igmp->csum)
        << "\nGroup:    " << ether_ntoa_r((ether_addr*)&igmp->group, (char*)group_addr) // need reentrant
        << '\n';
    ofs.flush();

    // Undefines
    #undef IGMPT
    #undef IGMPC
}

void Sniffer::printSTP(cuchar_cptr packet, c_uint len) {
    // Declarations
    stphdr *stp = (stphdr*)packet;
    unsigned char bid[ETH_PRINT_LEN],
                  rid[ETH_PRINT_LEN];

    // Zero Out
    std::memset(bid, 0, ETH_PRINT_LEN);
    std::memset(rid, 0, ETH_PRINT_LEN);   

    // Print Spanning Tree Protocol Header
    ofs << "\n~~~Spanning Tree Protocol Header~~~"
        << "\nProtocol ID:     " << ntohs(stp->protoID)
                                 << (ntohs(stp->protoID) == 0x0000 ? ": Spanning Tree Protocol"
                                   :                                 ": Unknown Protocol")
        << "\nVersion:         " << (unsigned)stp->version
                                 << ((unsigned)stp->version ==  0x00 ? ": Spanning Tree"
                                   : (unsigned)stp->version ==  0x02 ? ": Rapid Spanning Tree"
                                   : (unsigned)stp->version ==  0x03 ? ": Multiple Spanning Tree"
                                   :                                   ": Unknown Version")
        << "\nBPDU Type:       " << (unsigned)stp->msg_type
                                 << ((unsigned)stp->msg_type == 0x00 ? ": Configuration"
                                   : (unsigned)stp->msg_type == 0x02 ? ": RST/MST"
                                   : (unsigned)stp->msg_type == 0x80 ? ": TCN"
                                   :                                   ": Unknown Type")
        << "\nBPDU Flags:      " << (unsigned)stp->flags
        << "\nRoot Priority:   " << std::hex
                                 << (unsigned)stp->rootID[0] << ':'
                                 << (unsigned)stp->rootID[1]
                                 << std::dec
        << "\nRoot ID:         " << std::hex
                                 << (unsigned)stp->rootID[2] << ':'
                                 << (unsigned)stp->rootID[3] << ':'
                                 << (unsigned)stp->rootID[4] << ':'
                                 << (unsigned)stp->rootID[5] << ':'
                                 << (unsigned)stp->rootID[6] << ':'
                                 << (unsigned)stp->rootID[7]
                                 << std::dec
        << "\nRoot Path Cost:  " << ntohl(stp->root_pathCost)
        << "\nBridge Priority: " << std::hex
                                 << (unsigned)stp->bridgeID[0] << ':'
                                 << (unsigned)stp->bridgeID[1]
                                 << std::dec
        << "\nBridge ID:       " << std::hex
                                 << (unsigned)stp->bridgeID[2] << ':'
                                 << (unsigned)stp->bridgeID[3] << ':'
                                 << (unsigned)stp->bridgeID[4] << ':'
                                 << (unsigned)stp->bridgeID[5] << ':'
                                 << (unsigned)stp->bridgeID[6] << ':'
                                 << (unsigned)stp->bridgeID[7]
                                 << std::dec
        << "\nPort ID:         " << ntohs(stp->portID)
        << "\nMessage Age:     " << ntohs(stp->msg_age)
        << "\nMaximum Time:    " << ntohs(stp->max_time)
        << "\nHello Time:      " << ntohs(stp->hello_time)
        << "\nForward Delay:   " << ntohs(stp->fwrd_delay)
        << '\n';
    ofs.flush();
}

// Private Member Functions
int Sniffer::rfmon_up(c_char_ptrc ifc, int sfd) {
    // Declarations
    ifreq ifr;
    iwreq iwr;

    // Zero Out
    std::memset(&ifr, 0, sizeof(ifr));
    std::memset(&iwr, 0, sizeof(iwr));

    // Set Interface Down, ifr_flags = 0 from memset
    std::strncpy(ifr.ifr_name, ifc, IFNAMSIZ); // copy in interface device
    if(ioctl(sfd, SIOCSIFFLAGS, &ifr) == -1) { // set flags
        std::perror("rfmon_up: ioctl - SIOCSIFFLAGS-1");
        return -1;
    }

    // Get Mode
    std::strncpy(iwr.ifr_name, ifc, IFNAMSIZ); // copy in interface device
    if(ioctl(sfd, SIOCGIWMODE, &iwr) == -1) {
        std::perror("rfmon_up: ioctl - SIOCGIWMODE");
        return -1;
    }
 
    // Set Interface Mode
    std::strncpy(old_iwr.ifr_name, ifc, IFNAMSIZ); // copy in interface device
    iwr.u.mode = IW_MODE_MONITOR;                  // set monitor mode
    if(ioctl(sfd, SIOCSIWMODE, &iwr) == -1) {
        std::perror("rfmon_up: ioctl - SIOCSIWMODE");
        return -1;
    }

    // Bring Interface Up
    ifr.ifr_flags |= IFF_UP | IFF_BROADCAST | IFF_RUNNING; // OR in up, broadcast, running

    // Set Interface Flags
    if(ioctl(sfd, SIOCSIFFLAGS, &ifr) == -1) {
        std::perror("rfmon_up: ioctl - SIOCSIFFLAGS-2");
        return -1;
    }

    // Success
    return 0;
}

int Sniffer::rfmon_down(c_char_ptrc ifc, int sfd) {
    // Declarations
    ifreq ifr;
    iwreq iwr;

    // Zero Out
    std::memset(&ifr, 0, sizeof(ifr));
    std::memset(&iwr, 0, sizeof(iwr));   
    
    // Set Interface Down, ifr_flags = 0 from memset
    std::strncpy(ifr.ifr_name, ifc, IFNAMSIZ);     // copy in interface device
    if(ioctl(sfd, SIOCSIFFLAGS, &ifr) == -1) {     // set flags
        std::perror("rfmon_down: ioctl - SIOCSIFFLAGS-1");
        return -1;
    }

    // Set Interface Mode
    std::strncpy(old_iwr.ifr_name, ifc, IFNAMSIZ); // copy in interface device
    old_iwr.u.mode = IW_MODE_INFRA;                // not set, set managed mode
    if(ioctl(sfd, SIOCSIWMODE, &old_iwr) == -1) {
        std::perror("rfmon_down: ioctl - SIOCSIWMODE");
        return -1;
    }

    // Bring Interface Up
    old_ifr.ifr_flags |= IFF_UP | IFF_BROADCAST | IFF_RUNNING; // OR in up, broadcast, running

    // Set Interface Up
    std::strncpy(old_ifr.ifr_name, ifc, IFNAMSIZ); // copy in interface device
    if(ioctl(sfd, SIOCSIFFLAGS, &old_ifr) == -1) {
        std::perror("rfmon_down: ioctl - SIOCSIFFLAGS-2");
        return false;
    }

    // Success
    return 0;
}

int Sniffer::promisc_up(c_char_ptrc ifc, int sfd) {
    // Declarations
    ifreq ifr;

    // Zero Out
    std::memset(&ifr, 0, sizeof(ifr));

    // Get Interface Flags
    std::strncpy(ifr.ifr_name, ifc, IFNAMSIZ); // copy in interface device
    if((ioctl(sfd, SIOCGIFFLAGS, &ifr) == -1)) {
	    std::perror("promisc_up: ioctl - SIOCGIFFLAGS");
	    return -1;
	}

    // OR In Promiscuous
    if(ifr.ifr_flags & IFF_PROMISC)   // check if set ////////////////////////////////////////////////////////////////////////////////////////check if == IFF_PROMISC
        return 0;                     // already set
    else
        ifr.ifr_flags |= IFF_PROMISC; // not set, set promsicuous

    // Set Interface Flags   
    if(ioctl(sfd, SIOCSIFFLAGS, &ifr) == -1) {
        std::perror("promisc_up: ioctl - SIOCSIFFLAGS");
        return -1;
    }

    // Success
    return 0;
}

int Sniffer::promisc_down(c_char_ptrc ifc, int sfd) {
    // Declarations
    ifreq ifr;

    // Zero Out
    std::memset(&ifr, 0, sizeof(ifr));
     
    // Get Interface Flags
    std::strncpy(ifr.ifr_name, ifc, IFNAMSIZ); // copy in interface device
    if((ioctl(sfd, SIOCGIFFLAGS, &ifr) == -1)) {
	    std::perror("promisc_down: ioctl - SIOCGIFFLAGS");
	    return -1;
	}

    // AND Out Promiscuous
    if(ifr.ifr_flags & IFF_PROMISC)    // check if set///////////////////////////////////////////////////////////////////////////////////////same
        ifr.ifr_flags &= ~IFF_PROMISC; // unset promiscuous
    else
        return 0;                      // already set

    // Set Interface Flags
	if(ioctl(sfd, SIOCSIFFLAGS, &ifr) == -1) {
        std::perror("promisc_down: ioctl - SIOCSIFFLAGS");
        return -1;
    }

    // Success
    return 0;
}

int Sniffer::map_destruct() {
    // Unmap Memory
    if(munmap(ring, RING_FRAMES * getpagesize())) {
        std::perror("munmap");
        return -1;
    }

    // Success
    return 0;
}

int Sniffer::add_iface(char *dev) {
    // Declarations
    ifreq ifr;

    // Zero Out
    std::memset(&ifr, 0, sizeof(ifr));

    // Open TUN/TAP Driver Device
    int  fd = open("/dev/net/tun", O_RDWR);   
    if(fd < 0) {
        std::perror("open - O_RDWR");
        return -1; /* tun_alloc_old(dev) */
    }

    // Set Up Interface
    ifr.ifr_flags |= IFF_TAP; // TAP iface
    if(*dev) // kernel sets if dev = '\0'
        std::strncpy(ifr.ifr_name, "mon1", IFNAMSIZ);

    // Create Interface
    if(ioctl(fd, TUNSETIFF, (void*)&ifr) == -1) {
        std::perror("ioctl - TUNSETIFF");
        return -1;
    }

    /*// Get Hardware Address
    std::strncpy(ifr.ifr_name, "wlan0", IFNAMSIZ); // copy in interface device   
    if(ioctl(fd, SIOCGIFHWADDR, &ifr) == -1) {
        std::perror("ioctl - SIOCGIFHWADDR");
        return -1;
    }

    // Set Hardware Address
    std::strncpy(ifr.ifr_name, "mon1", IFNAMSIZ); // copy in interface device   
    if(ioctl(fd, SIOCSIFHWADDR, &ifr) == -1) {
        std::perror("ioctl - SIOCSIFHWADDR");
        return -1;
    }

    sockaddr_in addr;
    unsigned char buf[sizeof(in_addr)];

    std::memset(&addr, 0, sizeof(addr));
    std::memset(&buf,  0, sizeof(in_addr));

    // set the IP of this end point of tunnel
    std::strncpy(ifr.ifr_name, "wlan0", IFNAMSIZ); // copy in interface device   
    if(ioctl(fd, SIOCGIFADDR, ifr) == -1) {
        std::perror("ioctl - SIOCGIFADDR");
        return -1;
    }
            
    addr.sin_addr.s_addr = inet_pton(AF_INET, "192.168.0.8", buf); network byte order
    addr.sin_family      = AF_INET;
    std::memcpy(&ifr.ifr_addr, &addr, sizeof(sockaddr));

    std::strncpy(ifr.ifr_name, "mon1", IFNAMSIZ); // copy in interface device
   
    if(ioctl(fd, SIOCSIFADDR, ifr) == -1) {
        std::perror("ioctl - SIOCSIFADDR");
        return -1;
    }

    // Bring Interface Up
    ifr.ifr_flags |= IFF_UP | IFF_BROADCAST | IFF_RUNNING; // OR in up, broadcast, running

    // Set Interface Flags
    std::strncpy(ifr.ifr_name, "mon1", IFNAMSIZ); // copy in interface device   
    if(ioctl(fd, SIOCSIFFLAGS, &ifr) == -1) {
        std::perror("add_iface: ioctl - SIOCSIFFLAGS");
        return -1;
    }

    // Set MTU
    ifr.ifr_mtu = 65535;
    std::strncpy(ifr.ifr_name, "mon1", IFNAMSIZ); // copy in interface device   
    if(ioctl(fd, SIOCSIFMTU, &ifr) == -1) {
        std::perror("ioctl - SIOCSIFMTU");
        return -1;
    }*/

    // Set Our Device Name Value-Set Variable, kernel sets if = '\0'
    //if(*dev)
     //   std::strncpy(dev, ifr.ifr_name, IFNAMSIZ);

    // Success
    return fd; // return FD
}

int Sniffer::tunnel_out() {
    // Fork Program Flow
    pid_t cpid = fork();
    switch(cpid) {
    // Error
    case -1:
        std::perror("fork()");
        return -1;
    // Child
    case 0:
        // Infinite Loop, ARP Cache Poisoning
        for(;;) {
            //send_arp(smac, (cuchar_cptr)"192.168.0.1", (cuchar_cptr)"1D:3E:84:8A:4C:26", (cuchar_cptr)"192.168.0.2", 1); // S to V
            send_arp(smac, (cuchar_cptr)"192.168.0.2", (cuchar_cptr)"00:26:88:EA:84:80", (cuchar_cptr)"192.168.0.1", 1); // V to S
            usleep(400000); // slow down poisoning
        }

        // Shouldn't Get Here
        exit(EXIT_FAILURE);
    // Parent
    default:
        break;
    }
    return 0;
}

int Sniffer::send_arp(cuchar_cptr sha, cuchar_cptr sip,cuchar_cptr tha, cuchar_cptr tip, c_uint opcode) {
    // Declarations
    const unsigned PSIZE = sizeof(ieee80211_hdr3) + sizeof(llc_snap_hdr) + sizeof(arphdr2);
    unsigned char arpPacket[PSIZE];
    ieee80211_hdr3 *ie80211Spoof  = (ieee80211_hdr3*)arpPacket;
    llc_snap_hdr   *llc_snapSpoof = (llc_snap_hdr*)(ie80211Spoof  + sizeof(ieee80211_hdr3));
    arphdr2        *arpSpoof      = (arphdr2*)     (llc_snapSpoof + sizeof(llc_snap_hdr));
    ifreq ifr;
    sockaddr_ll destll, sll;

    //#define PACKET_QDISC_BYPASS 20

    // Create RAW Socket
    int sfdC = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ARP));
    if(sfdC == -1) {
        std::perror("socket");
        return -1;
    }

    // Get Interface Index
    std::strncpy(ifr.ifr_name, "mon0", IFNAMSIZ); // copy in interface device
    if(ioctl(sfdC, SIOCGIFINDEX, &ifr) == -1) {
        std::perror("ioctl - SIOCGIFINDEX");
        return false;
    }

    // Set Up Socket Link-Layer Address
    //sll.sll_ifindex  = ifr.ifr_ifindex;
    //sll.sll_family   = AF_PACKET;
    //sll.sll_protocol = htons(ETH_P_ALL);
    //sll.sll_hatype   = htons(ARPHRD_ETHER);
    //sll.sll_pkttype  = PACKET_OTHERHOST;
    //sll.sll_halen    = ETH_ALEN;
    //std::memcpy(&sll.sll_addr, smac, ETH_ALEN); // copy in

    // Bind RAW Socket
    //if(bind(sfdC, (sockaddr*)&sll, sizeof(sll))) {
        //std::perror("bind");
        //return false;
    //}

    // Bypass QDisk Layer, >= linux 3.14
    //int val = 1;
    //if(setsockopt(sfdC, SOL_PACKET, PACKET_QDISC_BYPASS, &val, sizeof(val))) {
        //std::perror("setsockopt - PACKET_QDISC_BYPASS");
        //return false;
    //}

    /*#define ETH_P_80211_RT	0x001B
    
    const unsigned char encap_eth[] {
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, // da       
        0x1d, 0x3e, 0x84, 0x8a, 0x4c, 0x26, // sa
        0x00, 0x1b, // ether_type
    };

    const unsigned char radiotaphdr1[] = {
        0x00, 0x00, // <-- radiotap version + pad
        0x19, 0x00, // <- radiotap header length
        0x90, 0x21, 0x00, 0x00, // <-- bitmap(it_present)
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // <-- timestamp
        0x10, // <-- tx_flags
        0x00, // <-- rate
        0x09, 0x85, // <-- channel
        0x04, 0x80, // <-- channel flags
        0x00, // <-- antsignal
        0x00, // <-- antnoise
        0x00, // <-- antenna
    };

    const unsigned char radiotaphdr[] = {
        0x00, 0x00, // <-- radiotap version
        0x0b, 0x00, // <- radiotap header length
        0x00, 0x80, 0x02, 0x00, // <-- bitmap
        0x00, // <-- rate
        0x00, // <-- tx power
        0x00, // <-- antenna
    };

    const unsigned char wifihdr[] = {
        0x88, 0x41, // frame control
        0x00, 0x00, // duration
        0xcc, 0x3a, 0x61, 0x15, 0x31, 0x9b, // addr2 bssid       
        0x1d, 0x3e, 0x84, 0x8a, 0x4c, 0x26, // addr1 sa
        0xcc, 0x3a, 0x61, 0x15, 0x31, 0x9b, // addr3 da
        0x40, 0x4f, // sequence control
    };

    const unsigned char llchdr[] = {
        0xaa, 0xaa, // dsap + ssap = SNAP(lsap)
        0x03, // control type = Unnumbered Information(UI)
        0x00, 0x00, 0x00, // rfc1042 oui
        0x08, 0x06 // ether_type arp
    };

    const unsigned char arpH[] = {
        0x00,  0x01, // hardware type eth 10mbps
        0x08,  0x00, // ether_type ip
        0x06, // hardware len(mac)
        0x04, // ether_type len(ip)
        0x00,  0x01, // opcode arp request
        0x1d, 0x3e, 0x84, 0x8a, 0x4c, 0x26, // sha
        0xc0, 0xa8, 0x2b, 0x33, // sip
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // tha
        0xc0, 0xa8, 0x2b, 0x01, // tip
    };*/

    const unsigned char packet[] = {
        // TPacketV2
        //0x00, 0x00, 0x00, 0x00, 0x26, 0x00, 0x00, 0x00, 0x26, 0x00, 0x00, 0x00, 0x50, 0x00, 0x50, 0x00,
        //0x78, 0x0E, 0xC4, 0x54, 0xC8, 0xFB, 0xAA, 0x10, 0x00, 0x00, 0x00, 0x00,

        // 16-Byte Bound Pad
        //0x00, 0x00, 0x00, 0x00,
        
        // SLL
        //0x11, 0x00, // family
        //0x00, 0x04, // proto
        //0x00, 0x00, 0x00, 0x004, // if_index
        //0x23, 0x03, // ha_type
        //0x03, // pkt_type
        //0x06, // ha_len
        //0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // addr
        
        // 16-Byte Bound Pad
        //0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

        // 16-Byte Bound Pad
        //0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        
        // radiotap
        /*0x00, // version
        0x00, // pad
        0x00, 0x11, // len
        0x30, 0x30, 0x00, 0x00, // present bitmap
        0x02, // rate
        0x00, // pad
        0x09, 0x6C, // <-- channel
        0x00, 0xC0, // <-- channel flags
        0x0C, // dbm_txpwr
        0x00, // antenna
        
        // ieee80211
        0x10, 0x80, // fc bitmap
        0x00, 0x00, // duration
        0x00, 0x26, 0x88, 0xEA, 0x84, 0x08, // addr1 bssid
        0x1D, 0x3F, 0x85, 0x8B, 0x4D, 0x27, // addr2 sa
        0x00, 0x26, 0x88, 0xEA, 0x84, 0x08, // addr3 da
        0x00, 0x00, // seq_ctrl
        
        // LLC
        0xAA, // dsap
        0xAA, // lsap
        0x03, // ctrl1
        
        // SNAP
        0x00, 0x00, 0x00, // oui
        0x08, 0x06, // ether_type
        
        // ARP
        0x00, 0x01, // ha_type
        0x08, 0x00, // ether_type
        0x06, // ha_len
        0x04, // ether_len
        0x00, 0x02, // opcode
        0x1D, 0x3F, 0x85, 0x8B, 0x4D, 0x27, // sha
        0xC0, 0xA8, 0x00, 0x01, // sip
        0x1C, 0x3E, 0x84, 0X8A, 0X4C, 0X26, // tha
        0XC0, 0XA8, 0X00, 0X08, // tip*/

        0x00, 0x00, 0x0E, 0x00, 0x00, 0x80, 0x0A, 0x00, 0x00, 0x00, 0x00, 0x07, 0x04, 0x00, 0x88, 0x41, 
        0x00, 0x00, 0x00, 0x26, 0x88, 0xEA, 0x84, 0x08, 0x1C, 0x3E, 0x84, 0x8A, 0x4C, 0x26, 0xFF, 0xFF, 
        0xFF, 0xFF, 0xFF, 0xFF, 0x50, 0x59, 0x00, 0x00, 0xA1, 0x05, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00,
        0xAA, 0xAA, 0x03, 0x00, 0x00, 0x00, 0x08, 0x06, 0x00, 0x01, 0x08, 0x00, 0x06, 0x04, 0x00, 0x01,
        0x1C, 0x3E, 0x84, 0x8A, 0x4C, 0x26, 0xC0, 0xA8, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0xC0, 0xA8, 0x00, 0x01,
    };

    /*#define SetToDs(pbuf) ({                        \
        *(unsigned short*)(pbuf) |= htole16(_TODS); \
    })
    
    #define SetFrDs(pbuf) ({                          \
        *(unsigned short*)(pbuf) |= htole16(_FROMDS); \
    })

    #define SetFrameType(pbuf, type)                                                \
        do {                                                                        \
            *(unsigned short*)(pbuf) &= __constant_cpu_to_le16(~(BIT(3) | BIT(2))); \
            *(unsigned short*)(pbuf) |= __constant_cpu_to_le16(type);               \
        }while(0)

    #define SetFrameSubType(pbuf, type)                                                                  \
        do {                                                                                             \
            *(unsigned short*)(pbuf) &= htole16(~(BIT(7) | BIT(6) | BIT(5) | BIT(4) | BIT(3) | BIT(2))); \
            *(unsigned short*)(pbuf) |= htole16(type);                                                   \
        }while(0)
    
    // Zero Out
    std::memset(&ifr,    0, sizeof(ifr));
    std::memset(&destll, 0, sizeof(destll));

    // Copy In Interface Device
    std::strncpy(ifr.ifr_name, iface, IFNAMSIZ);

    // Create Ethernet Header
    ie80211Spoof->frame_control = 0;
    ie80211Spoof->duration_id   = 0;
    ie80211Spoof->seq_ctrl      = 0;
    std::memcpy(ie80211Spoof->addr1, sha, ETH_ALEN); // BSSID
    std::memcpy(ie80211Spoof->addr2, tha, ETH_ALEN); // SA
    std::memcpy(ie80211Spoof->addr3, sha, ETH_ALEN); // DA
    SetToDs(ie80211Spoof);
    SetFrameType(ie80211Spoof, WIFI_DATA_FRAME);
    SetFrameSubType(ie80211Spoof, WIFI_DATA);

    // Create LLC SNAP Header
    llc_snapSpoof->dsap       = 170;
    llc_snapSpoof->ssap       = 170;
    llc_snapSpoof->ctrl1      = 3;
    llc_snapSpoof->oui1       = 0;
    llc_snapSpoof->oui2       = 0;
    llc_snapSpoof->ether_type = htons(ETH_P_ARP);

    // Create ARP Header
    arpSpoof->ar_hrd = htons(ARPHRD_ETHER);
    arpSpoof->ar_pro = htons(ETH_P_IP);
    arpSpoof->ar_hln = ETH_ALEN;
    arpSpoof->ar_pln = IP_ALEN;

    // Process Opcode
    if(opcode == 1)
        arpSpoof->ar_op = htons(ARPOP_REPLY);
    else if(opcode == 2);
        arpSpoof->ar_op = htons(ARPOP_REPLY);

    // Copy Addresses    
    std::memcpy(arpSpoof->ar_sha, sha, ETH_ALEN);
    std::memcpy(arpSpoof->ar_sip, sip, IP_ALEN);
    std::memcpy(arpSpoof->ar_tha, tha, ETH_ALEN);
    std::memcpy(arpSpoof->ar_tip, tip, IP_ALEN);
    
    // Copy In Interface Device
    std::strncpy(ifr.ifr_name, "mon0", IFNAMSIZ);

    // Get Interface Index
    if(ioctl(sfdC, SIOCGIFINDEX, iface) == -1) {
        std::perror("send_arp: ioctl - SIOCGIFINDEX");
        return -1;
    }*/

    // Set Up Socket Link-Layer Address
    destll.sll_ifindex  = ifr.ifr_ifindex;
    destll.sll_family   = AF_PACKET;
    destll.sll_protocol = htons(ETH_P_IP);
    destll.sll_hatype   = htons(ARPHRD_IEEE80211_RADIOTAP);
    destll.sll_pkttype  = PACKET_OUTGOING;
    destll.sll_halen    = ETH_ALEN;
    std::memcpy(&destll.sll_addr, sha, ETH_ALEN);
  
    tpacket2_hdr *buf = (tpacket2_hdr*)process_tx();
    std::memcpy(buf + (TPACKET2_HDRLEN - sizeof(sockaddr_ll)), packet, sizeof(packet));
    
    //unsigned char buf[sizeof(radiotaphdr) + sizeof(wifihdr) + sizeof(llchdr) + sizeof(arpH)];
    //std::memcpy(buf + buf->tp_mac , encap_eth, sizeof(encap_eth));
    //std::memcpy(buf, radiotaphdr, sizeof(radiotaphdr));
    //std::memcpy(buf + sizeof(radiotaphdr), wifihdr, sizeof(wifihdr));
    //std::memcpy(buf + sizeof(radiotaphdr) + sizeof(wifihdr), llchdr, sizeof(llchdr));
    //std::memcpy(buf + sizeof(radiotaphdr) + sizeof(wifihdr) + sizeof(llchdr), arpH, sizeof(arpH));

    // Prepare TPacket For Sending
    process_tx_release(sizeof(packet));

    // Send Spoofed Packet Back Out
    if(sendto(sfd, buf, sizeof(buf), 0, (sockaddr*)&destll, sizeof(sockaddr_ll)) == -1) {
        std::perror("sendto");
        return -1;
    }

    //if(write(sfd, buf, sizeof(buf)) == -1)
        //std::perror("write");

    // Success
    return 0;
}

//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
// eof sniffer.cpp

// Extra Stuff For Future
    /*// Process ToDS and FromDS Bits For Correct Addresses
    unsigned to_from_ds = ((GetToDS(ie80211_un) << 1) | GetFromDS(ie80211_un));
    switch(to_from_ds) {
        case 0x00: // 0 0
            flow = "\n Flow:                     STA -> STA (IBSS/DLS, Ad-hoc)";
            saddr1 = "\n Destination MAC Address:  ";
            saddr2 = "\n Source MAC Address:       ";
            saddr3 = "\n Basic Service Set ID:     ";
            break;
        case 0x01: // 0 1
            flow = "\n Flow:                     AP -> STA";
            saddr1 = "\n Destination MAC Address:  ";
            saddr2 = "\n Basic Service Set ID:     ";
            saddr3 = "\n Source MAC Address:       ";
            break;
        case 0x02: // 1 0
            flow = "\n Flow:                     STA -> AP";
            saddr1 = "\n Basic Service Set ID:     ";
            saddr2 = "\n Source MAC Address:       ";
            saddr3 = "\n Destination MAC Address:  ";
            break;
        case 0x03: // 1 1
            flow = "\nFlow: STA -> AP - > STA (Other BSS)";
            break;
      //default:
            // shouldn't happen
    }*/

    /*#ifndef SIOCSHWTSTAMP
    #define SIOCSHWTSTAMP 0x89b0
    #endif

    // Set Up Hardware Configuration For Time Stamping
	hwconfig.tx_type   = HWTSTAMP_TX_ON;         // stamp transmissions also 
	hwconfig.rx_filter = HWTSTAMP_FILTER_ALL;    // filter all
    ifr.ifr_data       = (void*)&hwconfig;
    std::strncpy(ifr.ifr_name, iface, IFNAMSIZ); // copy in interface device   
    if(ioctl(sfd, SIOCSHWTSTAMP, &ifr) == -1) {
        std::perror("createSniffer: ioctl - SIOCSHWTSTAMP");
        return false;
    }

    // Sync Hardware Timestamps To System Clock Through Pre-Pended Metadata
    int timeSource = SOF_TIMESTAMPING_SYS_HARDWARE; // sys clock
    if(setsockopt(sfd, SOL_PACKET, PACKET_TIMESTAMP, (void*)&timeSource, sizeof(timeSource))) {
        std::perror("setsockopt - PACKET_TIMESTAMP");
        return false;
    }*/
     
    // Process ARP Spoofing
            //if(((!std::strncmp(inet_ntoa(*(in_addr*)&arpH->ar_tip), "192.168.0.2", 15)   && // S to V
              //    std::strncmp(inet_ntoa(*(in_addr*)&arpH->ar_sip), "192.168.0.1", 15))  ||
                //(!std::strncmp(inet_ntoa(*(in_addr*)&arpH->ar_tip), "192.168.0.1", 15)   && // V to S
                 //!std::strncmp(inet_ntoa(*(in_addr*)&arpH->ar_sip), "192.168.0.2", 15))) && 
                 //*arpH->ar_sha != *smac)                                                    // not our mac
           //     send_arp(smac, arpH->ar_tip, arpH->ar_sha, arpH->ar_sip, 1);

        /*rc4_state state;
        if(GetPrivacy(ie80211_un)) {
            std::stringstream ss;
            std::string str;               
            ss << "ff237976ff91d017c8fb67d3f9";
            ss << llc->dsap << llc->ssap << llc->ctrl1;               
            ss >> str;
            rc4_init(&state, (u_char*)str.c_str(), str.length());
            rc4_crypt(&state, (u_char*)llc, (u_char*)llc, std::strlen((char*)packet) -
                      TPACKET2_HDRLEN - ie80211_Size - (sizeof(u8)*3));
            //int i = (*(int*)llc) ^ (*(int*)str.c_str());
            //std::memcpy((void*)llc, (const void*)&i, sizeof(i));
        }*/

