/*
 * sniffer.h
 * Description: Sniffer lass prototypes for netwrok sniffing.
 * (C) Copyright - Ryan Lockman
 * )))~3L1735~(((
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

// Macro
#ifndef SNIFFER_H
#define SNIFFER_H

// Headers
#include <fstream>
#include <cstdlib>
#include <cstring>

#include <unistd.h>
#include <arpa/inet.h>
#include <netinet/if_ether.h>
#include <linux/wireless.h>
#include <linux/if_packet.h>

#include "dumpParser.h" // local, homemade parser

// Sniffer Class
class Sniffer {
public:
// Typedefs
    typedef const unsigned char* const cuchar_cptr;
    typedef const char* const          c_char_ptrc;
    typedef const std::string          c_string;
    typedef const bool                 c_bool;
    typedef const unsigned             c_uint;

// Constructors
    Sniffer(c_char_ptrc interface, c_char_ptrc dumpPath, c_char_ptrc parsePath, c_bool pFlag,
            c_char_ptrc readablePath, c_string parse, c_bool rFlag, c_bool dFlag)
        : icmpC(0), igmpC(0), tcpC(0),  udpC(0),  sctpC(0), arpC(0),  paeC(0),
          tdlsC(0), stpC(0),  mgmtC(0), ctrlC(0), qosC(0),  dataC(0), extC(0),
          dataCtrlC(0), qosCtrlC(0),
          data_encryptC(0), 
          wdsC(0),
          otherDataLinkC(0),
          otherNetworkC(0),
          otherTransportC(0),
          dropC(0),
          incompleteC(0),
          totalPC(0),
          totalBC(0),
          parseDumpFlag(pFlag),
          readableDumpFlag(rFlag),
          debugFlag(dFlag),
          sfd(-1),
          rxring_offset(0),
          txring_offset(0),
          old_ifr(),
          old_iwr(),
          iface((char*)interface),
          pSavePath((char*)parsePath),
          ofs(dumpPath),
          readofs(readablePath),
          toParse(parse),
          Parser(),
          treq(),
          ring(NULL) { std::memset(smac, 0, ETH_ALEN); } // default
    ~Sniffer()       { if(is_valid()) close(sfd); }      // destructor

// Constant Member Functions
    int    getSockFD()               { return sfd; }
    ifreq  getSaved_IF()       const { return old_ifr; }
    iwreq  getSaved_IW()       const { return old_iwr; }
    c_bool is_valid()          const { return sfd != -1; }
    c_uint getICMP()           const { return icmpC; }
    c_uint getIGMP()           const { return igmpC; }
    c_uint getTCP()            const { return tcpC; }
    c_uint getUDP()            const { return udpC; }
    c_uint getSCTP()           const { return sctpC; }
    c_uint getARP()            const { return arpC; }
    c_uint getPAE()            const { return paeC; }
    c_uint getTDLS()           const { return tdlsC; }
    c_uint getSTP()            const { return stpC; }
    c_uint getMGMT()           const { return mgmtC; }
    c_uint getCTRL()           const { return ctrlC; }
    c_uint getQOS()            const { return qosC; }
    c_uint getQOSCtrl()        const { return qosCtrlC; }
    c_uint getEXT()            const { return extC; }
    c_uint getData()           const { return dataC; }
    c_uint getDataCtrl()       const { return dataCtrlC; }
    c_uint getDataEncrypt()    const { return data_encryptC; }
    c_uint getWDS()            const { return wdsC; }
    c_uint getOtherDataLink()  const { return otherDataLinkC; }
    c_uint getOtherNetwork()   const { return otherNetworkC; }
    c_uint getOtherTransport() const { return otherTransportC; }   
    c_uint getTotalP()         const { return totalPC; }
    c_uint getTotalB()         const { return totalBC; }
    c_uint getRxRingOffset()   const { return rxring_offset; }
    c_uint getTxRingOffset()   const { return txring_offset; }
    c_uint getDropedP()        const;
    c_uint getFreezeQCount()   const; // V3 Packet Only
    void   def_printSniffer()  const; // default print
    c_uint getLocalStoredDrop()       const { return dropC; }
    c_uint getLocalStoredIncomplete() const { return incompleteC; }

// Mutator Member Functions
    bool createSniffer(c_string packetType, const in_port_t port, c_bool rfmon, c_bool promisc, time_t secs, suseconds_t usecs);
    int  send_arp(cuchar_cptr sha, cuchar_cptr sip,cuchar_cptr tha, cuchar_cptr tip, c_uint opcode);   
    int  sniffPackets(),
         closeSniffer(c_bool monOff = true),
         tunnel_out();

private:
// Data Members
    // Counters
    unsigned       icmpC, igmpC, tcpC, udpC, sctpC,
                   arpC, paeC, tdlsC, stpC, 
                   mgmtC, ctrlC, qosC, dataC, extC,
                   dataCtrlC, qosCtrlC,
                   data_encryptC, wdsC,
                   otherDataLinkC, otherNetworkC, otherTransportC, // unknown
                   dropC, incompleteC,
                   totalPC, totalBC;
    // Flags
    bool           parseDumpFlag, readableDumpFlag, debugFlag; // dumping, debug
    // Misc.
    int            sfd, rxring_offset, txring_offset; // offsets, fd
    ifreq          old_ifr; // if request
    iwreq          old_iwr; // iw request
    char          *iface, *pSavePath; // interface, parse path
    std::ofstream  ofs, readofs; // outstreams
    std::string    toParse; // parse for
    DumpParser     Parser; // parser
    tpacket_req3   treq; // tpack request
    unsigned char *ring, // mmap ring
                   smac[ETH_ALEN]; // spoffed mac

// Private Functions
    // TPacket Functions
    void* process_rx();
    void* process_tx();
    void  process_rx_release();
    void  process_tx_release(c_uint len);
    unsigned nxt_pow_two(c_uint n); // V3 packet only

    // Filter Functions
    int attach_filter(c_char_ptrc ifc, cuchar_cptr smac, int sfd, c_uint fType);
    int raw_filter   (int sfd, cuchar_cptr mac_addr);
    
    // Packet Switching
    void packet_switch(const tpacket2_hdr *const packet, c_uint len);

    // Dumping And Printing Packet Data
    void header_dump   (cuchar_cptr packet, c_uint len);
    void readable_dump (cuchar_cptr packet, c_uint len);  
    void printTPACKET  (cuchar_cptr packet, c_uint len); // pre-pended
    void printSADDR_LL (cuchar_cptr packet, c_uint len); // pre-pended
    void printLLC      (cuchar_cptr packet, c_uint len);
    void printSNAP     (cuchar_cptr packet, c_uint len, c_bool eth_802_3);
    void print80211RTAP(cuchar_cptr packet, c_uint len); // pre-pended
    void printIEEE80211(cuchar_cptr packet, c_uint len);
    void printEthernet (cuchar_cptr packet, c_uint len, c_bool eth_802_3);
    void printIEEE8021X(cuchar_cptr packet, c_uint len);
    void printARP      (cuchar_cptr packet, c_uint len);
    void printIP_Proto (const char protocol);
    void printIP       (cuchar_cptr packet, c_uint len);
    void printTCP      (cuchar_cptr packet, c_uint len);
    void printUDP      (cuchar_cptr packet, c_uint len);
    void printSCTP     (cuchar_cptr packet, c_uint len);  
    void printICMP     (cuchar_cptr packet, c_uint len);
    void printIGMP     (cuchar_cptr packet, c_uint len);
    void printSTP      (cuchar_cptr packet, c_uint len);
    void print80211Status(const __le16 status);
    void print80211Reason(const __le16 reason);
    void printEtherType  (const __be16 h_proto);
    void printARP_HAType (const __be16 ar_hrd);  
    void printLSAP       (unsigned char lsap);
    void print80211ActionCat(const unsigned char category);
    
    // Socket And Mapping Functions
    int rfmon_up    (c_char_ptrc ifc, int sfd);
    int rfmon_down  (c_char_ptrc ifc, int sfd);
    int promisc_up  (c_char_ptrc ifc, int sfd);
    int promisc_down(c_char_ptrc ifc, int sfd);
    int map_destruct();
    int add_iface(char *dev);
};

#endif

