#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <stdarg.h>
#include <netinet/in.h>
#include <search.h>
#include <pcap.h>
#include <signal.h>
#include <arpa/inet.h>

#include "ndpi_main.h"

static void setupDetection(void);
static void node_output_flow_info_walker(const void *node, ndpi_VISIT which, int depth, void *user_data);
static void node_proto_guess_walker(const void *node, ndpi_VISIT which, int depth, void *user_data); 
int get_num_applications();
const char *ntos(uint32_t ip);

int print_on = 0;

static char *_pcap_file = NULL;


static char _pcap_error_buffer[PCAP_ERRBUF_SIZE];
static pcap_t *_pcap_handle = NULL;

static struct ndpi_detection_module_struct *ndpi_struct = NULL;
static u_int32_t detection_tick_resolution = 1000000; //microseconds

static u_int64_t raw_packet_count = 0;
static u_int64_t ip_packet_count = 0;
static u_int64_t total_bytes = 0;
static u_int64_t flow_counter_01 = 0;
static u_int64_t protocol_counter[NDPI_MAX_SUPPORTED_PROTOCOLS + NDPI_MAX_NUM_CUSTOM_PROTOCOLS + 1];
static u_int64_t protocol_counter_bytes[NDPI_MAX_SUPPORTED_PROTOCOLS + NDPI_MAX_NUM_CUSTOM_PROTOCOLS + 1];
static u_int32_t protocol_flows[NDPI_MAX_SUPPORTED_PROTOCOLS + NDPI_MAX_NUM_CUSTOM_PROTOCOLS + 1] = { 0 };
static int num_apps = 0;

static FILE *flow_info_file;
static char *flow_info_file_name;

static char labels[NDPI_MAX_SUPPORTED_PROTOCOLS + NDPI_MAX_NUM_CUSTOM_PROTOCOLS + 1][32];

static int del_unknown_flag = 0;
static int app_proto_only_flag = 0;

static int min_number_objects = 30;

#define	MAX_NDPI_FLOWS     20000000
#define IA_MAX             10000000

// id tracking
typedef struct ndpi_id {
    u_int8_t ip[4];
    struct ndpi_id_struct *ndpi_id;
} ndpi_id_t;


static u_int32_t size_id_struct = 0;

// flow tracking
typedef struct ndpi_flow {
    u_int32_t src_ip;
    u_int32_t dst_ip;
    u_int16_t src_port;
    u_int16_t dst_port;
    u_int32_t first_packet_time_sec;
    u_int32_t first_packet_time_usec;
    u_int8_t detection_completed, protocol;
    struct ndpi_flow_struct *ndpi_flow;
    
    //Flow features
    u_int16_t packets, bytes;
    u_int32_t last_packet_time_sec;
    u_int32_t last_packet_time_usec;
    double d_ia_time;
    double min_ia_time, max_ia_time;
    u_int32_t min_pkt_len, max_pkt_len;
    u_int8_t first_packet;

    // result only, not used for flow identification
    u_int16_t detected_protocol;

    void *src_id, *dst_id;
} ndpi_flow_t;


static u_int32_t size_flow_struct = 0;
static struct ndpi_flow *ndpi_flows_root = NULL;
static u_int32_t ndpi_flow_count = 0;
static u_int32_t valid_flow_count = 0; // 2+ packets in flow

static void *malloc_wrapper(unsigned long size) {
    return malloc(size);
}

static void free_wrapper(void *freeable) {
    free(freeable);
}

static char* ipProto2Name(u_short proto_id) {
    static char proto[8];

    switch(proto_id) {
    case IPPROTO_TCP:
        return("TCP");
        break;
    case IPPROTO_UDP:
        return("UDP");
        break;
    case IPPROTO_ICMP:
        return("ICMP");
        break;
    case 112:
        return("VRRP");
        break;
  }

  printf(proto, sizeof(proto), "%u", proto_id);
  return(proto);
}

static int node_cmp(const void *a, const void *b) {
    struct ndpi_flow *fa = (struct ndpi_flow*)a;
    struct ndpi_flow *fb = (struct ndpi_flow*)b;

    if(fa->src_ip < fb->src_ip) return(-1); else { if(fa->src_ip > fb->src_ip) return(1); }
    if(fa->src_port < fb->src_port) return(-1); else { if(fa->src_port > fb->src_port) return(1); }
    if(fa->dst_ip < fb->dst_ip) return(-1); else { if(fa->dst_ip > fb->dst_ip) return(1); }
    if(fa->dst_port < fb->dst_port) return(-1); else { if(fa->dst_port > fb->dst_port) return(1); }
    if(fa->protocol < fb->protocol) return(-1); else { if(fa->protocol > fb->protocol) return(1); }

  return(0);
}

static struct ndpi_flow *get_ndpi_flow(const struct pcap_pkthdr *header, const struct ndpi_iphdr *iph, u_int16_t ipsize) {
    u_int32_t i;
    u_int16_t l4_packet_len;
    struct ndpi_tcphdr *tcph = NULL;
    struct ndpi_udphdr *udph = NULL;
    u_int32_t src_ip;
    u_int32_t dst_ip;
    u_int16_t src_port;
    u_int16_t dst_port;
    struct ndpi_flow flow;
    void *ret;

    if (ipsize < 20) {
        return NULL;
    }

    if ((iph->ihl * 4) > ipsize || ipsize < ntohs(iph->tot_len) || (iph->frag_off & htons(0x1FFF)) != 0) {
        return NULL;
    }

    l4_packet_len = ntohs(iph->tot_len) - (iph->ihl * 4);

    src_ip = iph->saddr;
    dst_ip = iph->daddr;
   
    if (iph->protocol == 6 && l4_packet_len >= 20) {
        // tcp
        tcph = (struct ndpi_tcphdr *) ((u_int8_t *) iph + iph->ihl * 4);
        src_port = tcph->source;
        dst_port = tcph->dest;
       
    } else if (iph->protocol == 17 && l4_packet_len >= 8) {
        // udp
        udph = (struct ndpi_udphdr *) ((u_int8_t *) iph + iph->ihl * 4);
        src_port = udph->source;
        dst_port = udph->dest;
       
    } else {
        // non tcp/udp protocols
        src_port = 0;
        dst_port = 0;
    }

    flow.protocol = iph->protocol;
    flow.src_ip = src_ip;
    flow.dst_ip = dst_ip;
    flow.src_port = src_port;
    flow.dst_port = dst_port;
    flow.first_packet_time_sec = header->ts.tv_sec;
    flow.first_packet_time_usec = header->ts.tv_usec;

  

    ret = ndpi_tfind(&flow, (void*)&ndpi_flows_root, node_cmp);

    if(ret == NULL) {
        if (ndpi_flow_count == MAX_NDPI_FLOWS) {
            printf("ERROR: maximum flow count (%u) has been exceeded\n", MAX_NDPI_FLOWS);
            exit(-1);
        } else {
            struct ndpi_flow *newflow = (struct ndpi_flow*)malloc(sizeof(struct ndpi_flow));

            if(newflow == NULL) {
        	    printf("[NDPI] %s(1): not enough memory\n", __FUNCTION__);
        	    return(NULL);
            }

            memset(newflow, 0, sizeof(struct ndpi_flow));
            newflow->protocol = iph->protocol;
            newflow->src_ip = src_ip, newflow->dst_ip = dst_ip;
            newflow->src_port = src_port, newflow->dst_port = dst_port;
            newflow->first_packet_time_sec = header->ts.tv_sec;
            newflow->first_packet_time_usec = header->ts.tv_usec;
            newflow->last_packet_time_sec = header->ts.tv_sec;
            newflow->last_packet_time_usec = header->ts.tv_usec;
            newflow->d_ia_time = 0;
            newflow->min_ia_time = IA_MAX;
            newflow->max_ia_time = 0;
            newflow->min_pkt_len = header->len;
            newflow->max_pkt_len = header->len;
            newflow->first_packet = 1;          

            ndpi_tsearch(newflow, (void*)&ndpi_flows_root, node_cmp); /* Add */

            ndpi_flow_count += 1;

            //printFlow(newflow);
            return(newflow);
        }
    } else{
        return *(struct ndpi_flow**)ret;
    }
}

static void setupDetection(void) {
    u_int32_t i;
    NDPI_PROTOCOL_BITMASK all;

    // init global detection structure
    ndpi_struct = ndpi_init_detection_module();
    if (ndpi_struct == NULL) {
        printf("ERROR: global structure initialization failed\n");
        exit(-1);
    }
    // enable all protocols
    NDPI_BITMASK_SET_ALL(all);
    ndpi_set_protocol_detection_bitmask2(ndpi_struct, &all);

    // allocate memory for id and flow tracking
    size_id_struct = ndpi_detection_get_sizeof_ndpi_id_struct();
    size_flow_struct = ndpi_detection_get_sizeof_ndpi_flow_struct();

    // clear memory for results
    memset(protocol_counter, 0, sizeof(protocol_counter));
    memset(protocol_counter_bytes, 0, sizeof(protocol_counter_bytes));
    memset(protocol_flows, 0, sizeof(protocol_flows));

    raw_packet_count = ip_packet_count = total_bytes = 0;
    ndpi_flow_count = 0;
}

static void free_ndpi_flow(struct ndpi_flow *flow) {
    if(flow->ndpi_flow) { ndpi_free(flow->ndpi_flow); flow->ndpi_flow = NULL; }
    if(flow->src_id)    { ndpi_free(flow->src_id); flow->src_id = NULL;       }
    if(flow->dst_id)    { ndpi_free(flow->dst_id); flow->dst_id = NULL;       }
}

static void ndpi_flow_freer(void *node) {
    struct ndpi_flow *flow = (struct ndpi_flow*)node;
    free_ndpi_flow(flow);
    ndpi_free(flow);
}

static void terminateDetection(void) {
    ndpi_tdestroy(ndpi_flows_root, ndpi_flow_freer);
    ndpi_flows_root = NULL;
    ndpi_exit_detection_module(ndpi_struct);
}

static double get_inter_arrival_time(u_int32_t last_packet_time_sec, u_int32_t last_packet_time_usec, u_int32_t new_packet_time_sec, u_int32_t new_packet_time_usec) {
    u_int64_t last_time = ((uint64_t) last_packet_time_sec) * detection_tick_resolution + last_packet_time_usec / (1000000 / detection_tick_resolution);
    u_int64_t new_time = ((uint64_t) new_packet_time_sec) * detection_tick_resolution + new_packet_time_usec / (1000000 / detection_tick_resolution);
    double time = (double)(new_time - last_time);
    return time; 
}

static unsigned int packet_processing(const u_int64_t time, const struct pcap_pkthdr *header, const struct ndpi_iphdr *iph, u_int16_t ipsize, u_int16_t rawsize) {

    struct ndpi_id_struct *src, *dst;
    struct ndpi_flow *flow;
    struct ndpi_flow_struct *ndpi_flow = NULL;
    u_int16_t protocol = 0;
    u_int16_t frag_off = ntohs(iph->frag_off);
    double ia_time;

    flow = get_ndpi_flow(header, iph, ipsize);
    if (flow != NULL) {

        ndpi_flow = flow->ndpi_flow;
        flow->packets++, flow->bytes += rawsize;
        src = flow->src_id, dst = flow->dst_id;
        ia_time = get_inter_arrival_time(flow->last_packet_time_sec, flow->last_packet_time_usec, header->ts.tv_sec, header->ts.tv_usec);
        flow->d_ia_time+=ia_time;
        
        if(flow->first_packet != 1) {
            if(ia_time < flow->min_ia_time){ flow->min_ia_time = ia_time; }
            if(ia_time > flow->max_ia_time){ flow->max_ia_time = ia_time; }
        }
        flow->first_packet = 0;
        
        if(header->len < flow->min_pkt_len){flow->min_pkt_len = header->len;}
        if(header->len > flow->max_pkt_len){flow->max_pkt_len = header->len;}
        
        flow->last_packet_time_sec = header->ts.tv_sec;
        flow->last_packet_time_usec = header->ts.tv_usec;
        
    } else {
        return 0;
    }

    ip_packet_count++;
    total_bytes += rawsize;


    // here the actual detection is performed
    ndpi_protocol detected = ndpi_detection_process_packet(ndpi_struct, ndpi_flow, (uint8_t *) iph, ipsize, time, src, dst);
    protocol = detected.app_protocol;

    if(protocol==0){
        detected = ndpi_guess_undetected_protocol(ndpi_struct, flow->protocol, ntohl(flow->src_ip), ntohs(flow->src_port), ntohl(flow->dst_ip), ntohs(flow->dst_port));
        if(detected.app_protocol!=detected.master_protocol){        
            protocol = detected.app_protocol;
        }          
    }

    flow->detected_protocol = protocol;
    

    if((flow->detected_protocol != NDPI_PROTOCOL_UNKNOWN) || (iph->protocol == IPPROTO_UDP) || ((iph->protocol == IPPROTO_TCP) && (flow->packets > 100))) {
        flow->detection_completed = 1;
        free_ndpi_flow(flow);        
    }

  return 0;
}

// executed for each packet in the pcap file
static void pcap_packet_callback(u_char * args, const struct pcap_pkthdr *header, const u_char * packet) {
  
    const struct ndpi_ethhdr *ethernet = (struct ndpi_ethhdr *) packet;
    struct ndpi_iphdr *iph = (struct ndpi_iphdr *) &packet[sizeof(struct ndpi_ethhdr)];
    u_int64_t time;
    static u_int64_t lasttime = 0;
    u_int16_t type, ip_offset;

    raw_packet_count++;

    time = ((uint64_t) header->ts.tv_sec) * detection_tick_resolution + header->ts.tv_usec / (1000000 / detection_tick_resolution);

    type = ethernet->h_proto;

    if (type != 8 || iph->version != 4) {
       // printf("WARNING: only IPv4 packets are supported\n");
        return;
    }

    ip_offset = sizeof(struct ndpi_ethhdr);
    
    // process the packet
    packet_processing(time, header, iph, header->len - ip_offset, header->len);
  
}

static int valid_label(char *app_name){
    for(int i=0; i < num_apps; i++){
        if(strcmp(labels[i], app_name) == 0) {
            return 1;
        }            
    }
    return 0;
}


const char *ntos(uint32_t ip)
{   
    char *str=(char*)malloc(17);

    unsigned char ip_str[4];
    ip_str[0] = ip & 0xFF;
    ip_str[1] = (ip >> 8) & 0xFF;
    ip_str[2] = (ip >> 16) & 0xFF;
    ip_str[3] = (ip >> 24) & 0xFF;

    snprintf(str, 16, "%d.%d.%d.%d",
                 ip_str[0], ip_str[1], ip_str[2], ip_str[3]);

    return str; 
}

static void printFlow(struct ndpi_flow *flow, FILE *file) {
    if (flow->packets < 2 || valid_label(ndpi_get_proto_name(ndpi_struct, flow->detected_protocol)) == 0 ) { return; }
    double last_time = (flow->last_packet_time_sec) * detection_tick_resolution + flow->last_packet_time_usec / (1000000 / detection_tick_resolution);
    double first_time = (flow->first_packet_time_sec) * detection_tick_resolution + flow->first_packet_time_usec / (1000000 / detection_tick_resolution);
    double duration = last_time - first_time; 

    const char* src = ntos(flow->src_ip);  
    const char* dst = ntos(flow->dst_ip);  
    
   
    fprintf(file, "%s,%u,%s,%u,%s,%.6f,%.6f,%.6f,%u,%u,%.6f,%.6f,%.6f,%u,%u,%u,%.6f,%.6f,%s\n",
        src,
        ntohs(flow->src_port),
        dst,
        ntohs(flow->dst_port),
        ipProto2Name(flow->protocol),
        first_time,
        last_time,
        duration,
        flow->bytes,
        flow->packets,
        (double)(flow->d_ia_time/((double)flow->packets-1)),
        flow->min_ia_time,
        flow->max_ia_time,
        flow->bytes/flow->packets,
        flow->min_pkt_len,
        flow->max_pkt_len,
        ((double)flow->packets/duration)*1000*1000,
        ((double)flow->bytes/duration)*1000*1000,
        ndpi_get_proto_name(ndpi_struct, flow->detected_protocol)
    );

}

static void printResults(void) {
    
    ndpi_twalk(ndpi_flows_root, node_proto_guess_walker, NULL);
    num_apps = get_num_applications();
    flow_info_file = fopen(flow_info_file_name, "wb");
    fprintf(flow_info_file, "%i,13,%i\n", valid_flow_count, num_apps);    
    for(int i=0; i < num_apps; i++){
        fprintf(flow_info_file,"%s,",labels[i]);
    }    
    fprintf(flow_info_file,"\n");

    fputs("source_ip,source_port,dest_ip,dest_port,IP4_proto,f_start,f_end,f_dur,delta_bytes,delta_packets,avg_ia,min_ia,max_ia,avg_len,min_len,max_len,pkt_vel,byte_vel,application\n", flow_info_file);
    ndpi_twalk(ndpi_flows_root, node_output_flow_info_walker, NULL);
    fclose(flow_info_file);
    
    
}

static void node_output_flow_info_walker(const void *node, ndpi_VISIT which, int depth, void *user_data) {
    struct ndpi_flow *flow = *(struct ndpi_flow**)node;
    if (flow_info_file != NULL){
        if ((which == preorder) || (which == leaf)) {           
           printFlow(flow, flow_info_file);
        }
        
    }else {printf("Invalid file stream!\n"); exit(-1);}
       
}

static void node_proto_guess_walker(const void *node, ndpi_VISIT which, int depth, void *user_data) {
    struct ndpi_flow *flow = *(struct ndpi_flow**)node;
    if((which == preorder) || (which == leaf)) { /* Avoid walking the same node multiple times */
        if (flow->packets > 1 ) {
            protocol_counter[flow->detected_protocol]       += flow->packets;
            protocol_counter_bytes[flow->detected_protocol] += flow->bytes;
            protocol_flows[flow->detected_protocol]++;    
            //valid_flow_count++;
        }
    }    
}

int get_num_applications(){
    int num_apps = 0;  
    int label_i = 0;  
    for(int i=0; i < NDPI_MAX_SUPPORTED_PROTOCOLS + NDPI_MAX_NUM_CUSTOM_PROTOCOLS; i++){
        if(protocol_flows[i] >= min_number_objects) {
            num_apps++;
            valid_flow_count+=protocol_flows[i];
            strcpy(labels[label_i] ,ndpi_get_proto_name(ndpi_struct, i));
            label_i++;            
        }
    }
    return num_apps;
}

int main(int argc, char *argv[]) {

    if(argc<3){
        printf("Please provide a tcpdump file and output file name\n");
        return(-1);
    }

    if(argc == 4){
        min_number_objects = *argv[3];
    }        

   
    pcap_t *handle; //store the "device" (from tcpdump)

    handle = pcap_open_offline(argv[1],NULL);

    if(handle==NULL){
       printf("Couldn't open the file %s\n", argv[1]);
       return(-1);
    }    
    
    setupDetection();

    pcap_loop(handle, -1, pcap_packet_callback, NULL);

    pcap_close(handle);

    flow_info_file_name = argv[2];
  
    printResults();


return 0;
}

