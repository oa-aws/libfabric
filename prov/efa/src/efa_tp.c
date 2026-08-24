/* SPDX-License-Identifier: BSD-2-Clause OR GPL-2.0-only */
/* SPDX-FileCopyrightText: Copyright Amazon.com, Inc. or its affiliates. All rights reserved. */

#include "efa_tp.h"
#include <pthread.h>

#if HAVE_ESP

#include "efa.h"
#include "efa_device.h"
#include "efa_io_defs.h"

#define ESP_EFA_SEND_TYPE_COUNT 3

/* Global metrics */
static esp_level_counter_t wqe_inflight_reqs_counter = NULL;
static esp_level_counter_t wqe_inflight_bytes_counter = NULL;
static esp_level_counter_t wqe_estimated_bw_counter = NULL;

static esp_global_histogram_t wqe64_latency_histogram = NULL;
static esp_global_histogram_t wqe_latency_histogram = NULL;
static esp_global_histogram_t wqe_size_histogram = NULL;

/* Number of wqes sent in each batch before ringing doorbell. */
static esp_global_histogram_t wqe_batch_size_histogram = NULL;

/* Ring doorbell latency*/
static __thread esp_histogram_t efa_data_path_direct_send_wr_ring_db_latency =
	ESP_THREAD_LOCAL_VAR_REQUIRES_INIT;

/* poll_cq profiling*/
static __thread esp_histogram_t efa_cq_readfrom_host_histogram =
	ESP_THREAD_LOCAL_VAR_REQUIRES_INIT;
static __thread esp_histogram_t efa_cq_readfrom_device_histogram =
	ESP_THREAD_LOCAL_VAR_REQUIRES_INIT;
static esp_global_histogram_t efa_cq_readfrom_count = NULL;

/* Per-device metrics */
struct esp_wqe_metrics_t {
	esp_level_counter_t *wqe_inflight_reqs_counters;
	esp_level_counter_t *wqe_inflight_bytes_counters;
	esp_level_counter_t *wqe_estimated_bw_counters;

	esp_global_histogram_t *wqe64_latency_histograms;
	esp_global_histogram_t *wqe_latency_histograms;
	esp_global_histogram_t *wqe_size_histograms;
};

/* Global metrics. */
static struct esp_wqe_metrics_t wqe_metrics[ESP_EFA_SEND_TYPE_COUNT] = {};

static const char *op_names[ESP_EFA_SEND_TYPE_COUNT] = {"send", "read",
							"write"};

static uint64_t op_type_name_ids[ESP_EFA_SEND_TYPE_COUNT] = {};

/* Global flags. */
static int esp_current_rank_enabled = 0;
static int esp_enable_counter_data = 0;
static int esp_enable_per_device_data = 0;
static int esp_enable_bw_data = 0;
static int esp_enable_door_bell_data = 0;
static int esp_enable_poll_data = 0;
static int esp_enable_recv_data = 0;
static int esp_enable_trace = 0;

/* Trie for device name cache (per-thread) */
static __thread esp_trie_t esp_dev_name_cache = NULL;

/* Latency bin generator constants: */
#define BIN_COUNT 54
/* One bin for small latency samples */
#define LOWER_BOUND 2000
/* 32 bins for median part, each bin 250 nanos wide */
#define MEDIAN_BOUND	 10000
#define MEDIAN_BIN_SIZE	 250
#define MEDIAN_BIN_COUNT 32
/* 10 bins for higher part, each bin 1 micro wide */
#define UPPER_BOUND	20000
#define UPPER_BIN_SIZE	1000
#define UPPER_BIN_COUNT 10

/* Last 10 bins (tail) has bin size the increases exponentially. */
static uint64_t bin_bounds[BIN_COUNT] = {};

/* Initialize custom latency histogram bins. */
static void init_bin_bounds()
{
	/* Below body: single bin for up to 2 micros. */
	bin_bounds[0] = LOWER_BOUND;
	size_t bin_count = 1;

	/* Median: 32 bins, 250 nanos wide, up to 10 micros. */
	for (uint32_t i = 0; i < MEDIAN_BIN_COUNT; ++i) {
		bin_bounds[bin_count] =
			bin_bounds[bin_count - 1] + MEDIAN_BIN_SIZE;
		++bin_count;
	}

	/* Shoulder: 10 bins, 1 micros wide, range 10-20 micros. */
	for (uint32_t i = 0; i < UPPER_BIN_COUNT; ++i) {
		bin_bounds[bin_count] =
			bin_bounds[bin_count - 1] + UPPER_BIN_SIZE;
		++bin_count;
	}

	/* Tail: logarithm from 1 micros bin up to 512 micros wide bin (12
	 * bins), total range 20-1171 micros. */
	uint64_t bin_width = UPPER_BIN_SIZE;
	for (uint32_t i = bin_count; i < BIN_COUNT - 1; ++i) {
		bin_bounds[i] = bin_bounds[i - 1] + bin_width;
		bin_width *= 2;
	}
	bin_bounds[BIN_COUNT - 1] = UINT64_MAX;
}

/* Custom bin generator callback */
static uint64_t get_bin_count(struct esp_bin_generator_s *bin_generator)
{
	return BIN_COUNT;
}

/* Custom bin generator callback */
static uint64_t select_bin(struct esp_bin_generator_s *bin_generator,
			   uint64_t sample)
{
	/* NOTE: sample is already in nanoseconds. */

	/* Below body: single bin for up to 2 micros. */
	if (sample < LOWER_BOUND) {
		return 0;
	}

	/* Median: 32 bins, 250 nanos wide, up to 10 micros. */
	if (sample < MEDIAN_BOUND) {
		return 1 + (sample - LOWER_BOUND) / MEDIAN_BIN_SIZE;
	}

	/* Shoulder: 10 bins, 1 micros wide, range 10-20 micros. */
	if (sample < UPPER_BOUND) {
		return 1 + MEDIAN_BIN_COUNT +
		       (sample - MEDIAN_BOUND) / UPPER_BIN_SIZE;
	}

	/* Tail: logarithm from 1 micros bin up to 512 micros wide bin (12
	 * bins), total range 20-1171 micros. */
	uint64_t bit =
		__builtin_clzll((sample - UPPER_BOUND) / UPPER_BIN_SIZE + 1);
	uint64_t bitIndex = 63 - bit;
	uint64_t binIndex = 1 + MEDIAN_BIN_COUNT + UPPER_BIN_COUNT + bitIndex;
	if (binIndex >= BIN_COUNT) {
		binIndex = BIN_COUNT - 1;
	}
	return binIndex;
}

/* Custom bin generator callback */
static uint64_t get_bin_bound(struct esp_bin_generator_s *bin_generator,
			      uint64_t bin_index)
{
	/* NOTE: Bin bounds are in nanoseconds. */
	return bin_index < BIN_COUNT ? bin_bounds[bin_index] : UINT64_MAX;
}

/* Custom bin generator callback */
static int load_bin_generator(struct esp_bin_generator_s *bin_generator,
			      uint64_t *args, size_t nargs)
{
	return ENOTSUP;
}

/* Custom bin generator callback */
static void destroy_bin_generator(struct esp_bin_generator_s *)
{
}

/* Custom bin generator callback */
static struct esp_bin_generator_s *
clone_bin_generator(struct esp_bin_generator_s *bin_generator)
{
	struct esp_bin_generator_s *res = (struct esp_bin_generator_s *) calloc(
		1, sizeof(struct esp_bin_generator_s));
	if (res != NULL) {
		res->get_bin_count = get_bin_count;
		res->select_bin = select_bin;
		res->get_bin_bound = get_bin_bound;
		res->load = load_bin_generator;
		res->clone = clone_bin_generator;
		res->destroy = destroy_bin_generator;
	}
	return res;
}

/* Latency custom bin generator */
esp_bin_generator_t latency_bin_generator = {.get_bin_count = get_bin_count,
					     .select_bin = select_bin,
					     .get_bin_bound = get_bin_bound,
					     .load = load_bin_generator,
					     .clone = clone_bin_generator,
					     .destroy = destroy_bin_generator};

/* Trace records */

/* data_path_direct_base record */
ESP_BEGIN_TRACE_DEF(data_path_direct_base)
ESP_TRACE_DEF_STR_MEMBER(dev_name)
ESP_TRACE_DEF_MEMBER(uint32_t, src_qp_num)
ESP_TRACE_DEF_MEMBER(uint32_t, dst_qp_num)
ESP_TRACE_DEF_MEMBER(uint16_t, ah_num)
ESP_TRACE_DEF_MEMBER(uint32_t, length)
ESP_TRACE_DEF_MEMBER(uint64_t, wr_idx)
ESP_TRACE_DEF_MEMBER(uint32_t, dev_id)
ESP_END_TRACE_DEF_LOCAL(data_path_direct_base)

/* data_path_direct_post_send record */
ESP_BEGIN_TRACE_DEF_EXT(data_path_direct_post_send, data_path_direct_base)
ESP_TRACE_DEF_STR_MEMBER(op_type)
ESP_TRACE_DEF_MEMBER(uint64_t, wr_id)
ESP_END_TRACE_DEF_LOCAL(data_path_direct_post_send)

/* data_path_direct_process_completion record */
ESP_BEGIN_TRACE_DEF_EXT(data_path_direct_process_completion,
			data_path_direct_base)
ESP_TRACE_DEF_MEMBER(const struct ibv_cq_ex *, ibvcqx)
ESP_TRACE_DEF_MEMBER(int, opcode)
ESP_END_TRACE_DEF_LOCAL(data_path_direct_process_completion)

/* esp_data_path_direct_post_recv record */
ESP_BEGIN_TRACE_DEF(data_path_direct_post_recv)
ESP_TRACE_DEF_STR_MEMBER(dev_name)
ESP_TRACE_DEF_MEMBER(uint64_t, wr_id)
ESP_TRACE_DEF_MEMBER(uint32_t, qp_num)
ESP_TRACE_DEF_MEMBER(int, num_sge)
ESP_END_TRACE_DEF_LOCAL(data_path_direct_post_recv)

static inline uint32_t efa_get_wqe_length(const struct efa_io_tx_wqe_128 *wqe)
{
	enum efa_io_send_op_type op_type;
	uint32_t length = 0;

	op_type = EFA_GET(&wqe->meta.ctrl1, EFA_IO_TX_META_DESC_OP_TYPE);
	switch (op_type) {
	case EFA_IO_SEND:
		if (EFA_GET(&wqe->meta.ctrl1, EFA_IO_TX_META_DESC_INLINE_MSG))
			return wqe->meta.length;
		for (size_t i = 0; i < wqe->meta.length; i++)
			length += wqe->data.sgl[i].length;
		return length;
	case EFA_IO_RDMA_READ:
	case EFA_IO_RDMA_WRITE:
		return wqe->data.rdma_req.remote_mem.length;
	}
	return 0;
}

/* Load runtime configuration from env. */
static int esp_load_env(const char *env_var_name)
{
	int res = 0;
	char *env_str = getenv(env_var_name);
	if (env_str != NULL) {
		if (strcasecmp(env_str, "true") == 0 ||
		    strcasecmp(env_str, "yes") == 0 ||
		    strcasecmp(env_str, "on") == 0) {
			EFA_INFO(FI_LOG_CORE,
				 "Loaded profiling configuration from env "
				 "%s=TRUE\n",
				 env_var_name);
			res = 1;
		} else if (strcasecmp(env_str, "false") == 0 ||
			   strcasecmp(env_str, "no") == 0 ||
			   strcasecmp(env_str, "off") == 0) {
			EFA_INFO(FI_LOG_CORE,
				 "Loaded profiling configuration from env "
				 "%s=FALSE\n",
				 env_var_name);
			res = 0;
		} else {
			EFA_WARN(FI_LOG_CORE, "Invalid value for %s: %s\n",
				 env_var_name, env_str);
		}
	}
	return res;
}

/* Initialize per-device profile object arrays. */
static void init_per_device_wqe_metrics()
{
	unsigned i = 0;
	for (i = 0; i < ESP_EFA_SEND_TYPE_COUNT; ++i) {
		wqe_metrics[i].wqe_inflight_reqs_counters =
			(esp_level_counter_t *) calloc(
				1, sizeof(esp_level_counter_t) *
					   g_efa_selected_device_cnt);
		wqe_metrics[i].wqe_inflight_bytes_counters =
			(esp_level_counter_t *) calloc(
				1, sizeof(esp_level_counter_t) *
					   g_efa_selected_device_cnt);

		if (esp_enable_bw_data) {
			wqe_metrics[i].wqe_estimated_bw_counters =
				(esp_level_counter_t *) calloc(
					1, sizeof(esp_level_counter_t) *
						   g_efa_selected_device_cnt);
		}

		wqe_metrics[i].wqe64_latency_histograms =
			(esp_global_histogram_t *) calloc(
				1, sizeof(esp_global_histogram_t) *
					   g_efa_selected_device_cnt);
		wqe_metrics[i].wqe_latency_histograms =
			(esp_global_histogram_t *) calloc(
				1, sizeof(esp_global_histogram_t) *
					   g_efa_selected_device_cnt);
		wqe_metrics[i].wqe_size_histograms =
			(esp_global_histogram_t *) calloc(
				1, sizeof(esp_global_histogram_t) *
					   g_efa_selected_device_cnt);
	}
}

/* Initialize per-device profile object arrays. */
static void term_per_device_wqe_metrics()
{
	unsigned i = 0;
	for (i = 0; i < ESP_EFA_SEND_TYPE_COUNT; ++i) {
		if (wqe_metrics[i].wqe_inflight_reqs_counters != NULL) {
			free(wqe_metrics[i].wqe_inflight_reqs_counters);
			wqe_metrics[i].wqe_inflight_reqs_counters = NULL;
		}
		if (wqe_metrics[i].wqe_inflight_bytes_counters != NULL) {
			free(wqe_metrics[i].wqe_inflight_bytes_counters);
			wqe_metrics[i].wqe_inflight_bytes_counters = NULL;
		}

		if (esp_enable_bw_data) {
			if (wqe_metrics[i].wqe_estimated_bw_counters != NULL) {
				free(wqe_metrics[i].wqe_estimated_bw_counters);
				wqe_metrics[i].wqe_estimated_bw_counters = NULL;
			}
		}

		if (wqe_metrics[i].wqe64_latency_histograms != NULL) {
			free(wqe_metrics[i].wqe64_latency_histograms);
			wqe_metrics[i].wqe64_latency_histograms = NULL;
		}
		if (wqe_metrics[i].wqe_latency_histograms != NULL) {
			free(wqe_metrics[i].wqe_latency_histograms);
			wqe_metrics[i].wqe_latency_histograms = NULL;
		}
		if (wqe_metrics[i].wqe_size_histograms != NULL) {
			free(wqe_metrics[i].wqe_size_histograms);
			wqe_metrics[i].wqe_size_histograms = NULL;
		}
	}
}

/* Initialize global profile objects. */
static void init_wqe_metrics()
{
	wqe_inflight_reqs_counter = esp_get_level_counter(
		"wqe_inflight_reqs", ESP_COUNTING_COUNTER, "", 1);
	wqe_inflight_bytes_counter = esp_get_level_counter(
		"wqe_inflight_bytes", ESP_COUNTING_COUNTER, "", 1);

	if (esp_enable_bw_data) {
		wqe_estimated_bw_counter = esp_get_level_counter(
			"wqe_estimated_bw", ESP_COUNTING_COUNTER, "Gbps", 1);
	}

	wqe64_latency_histogram = esp_get_global_histogram(
		"wqe64_latency", &latency_bin_generator, 1, 1, "ns", 1);
	wqe_latency_histogram = esp_get_global_histogram(
		"wqe_latency", &latency_bin_generator, 1, 1, "ns", 1);
	wqe_size_histogram = esp_get_global_histogram(
		"wqe_size", ESP_LOG2_BIN_GENERATOR(), 0, 1, "bytes", 1);

	wqe_batch_size_histogram = esp_get_global_histogram(
		"wqe_bratch_size", ESP_LINEAR_BIN_GENERATOR(1, 16, 0), 0, 1,
		"wqes", 1);

	efa_cq_readfrom_count = esp_get_global_histogram(
		"efa_cq_readfrom_count", ESP_LINEAR_BIN_GENERATOR(1, 10, 0), 0,
		1, "", 1);
}

static int esp_init_traces()
{
	/* data_path_direct_base record */
	ESP_BEGIN_IMPLEMENT_TRACE_DEF(data_path_direct_base)
	ESP_TRACE_IMPLEMENT_STR_MEMBER(dev_name)
	ESP_TRACE_IMPLEMENT_UINT32_MEMBER(src_qp_num)
	ESP_TRACE_IMPLEMENT_UINT32_MEMBER(dst_qp_num)
	ESP_TRACE_IMPLEMENT_UINT16_MEMBER(ah_num)
	ESP_TRACE_IMPLEMENT_UINT32_MEMBER(length)
	ESP_TRACE_IMPLEMENT_UINT64_MEMBER(wr_idx)
	ESP_TRACE_IMPLEMENT_UINT32_MEMBER(dev_id)
	ESP_END_IMPLEMENT_TRACE_DEF()

	/* data_path_direct_post_send record */
	ESP_BEGIN_IMPLEMENT_TRACE_DEF_EXT(data_path_direct_post_send,
					  data_path_direct_base)
	ESP_TRACE_IMPLEMENT_STR_MEMBER(op_type)
	ESP_TRACE_IMPLEMENT_INT64_MEMBER(wr_id)
	ESP_END_IMPLEMENT_TRACE_DEF()

	/* data_path_direct_process_completion record */
	ESP_BEGIN_IMPLEMENT_TRACE_DEF_EXT(data_path_direct_process_completion,
					  data_path_direct_base)
	ESP_TRACE_IMPLEMENT_PTR_MEMBER(ibvcqx)
	ESP_TRACE_IMPLEMENT_INT32_MEMBER(opcode)
	ESP_END_IMPLEMENT_TRACE_DEF()

	/* data_path_direct_post_recv record */
	ESP_BEGIN_IMPLEMENT_TRACE_DEF(data_path_direct_post_recv)
	ESP_TRACE_IMPLEMENT_STR_MEMBER(dev_name)
	ESP_TRACE_IMPLEMENT_UINT64_MEMBER(wr_id)
	ESP_TRACE_IMPLEMENT_UINT32_MEMBER(qp_num)
	ESP_TRACE_IMPLEMENT_INT32_MEMBER(num_sge)
	ESP_END_IMPLEMENT_TRACE_DEF()

	/* Allocate op-type shared names. */
	op_type_name_ids[EFA_IO_SEND] = esp_alloc_shared_name("send");
	op_type_name_ids[EFA_IO_RDMA_READ] = esp_alloc_shared_name("read");
	op_type_name_ids[EFA_IO_RDMA_WRITE] = esp_alloc_shared_name("write");

	/* Execute trace record registration. */
	return esp_register_trace_exec();
}

static void cleanup_dev_name_cache(void * /* unused */)
{
	if (esp_dev_name_cache != NULL) {
		esp_trie_destroy(esp_dev_name_cache);
		esp_dev_name_cache = NULL;
	}
}

static uint64_t get_dev_name_id(const char *dev_name)
{
	uint64_t dev_id = UINT64_MAX;
	if (esp_dev_name_cache == NULL) {
		/* Create cache on-demand for current thread. */
		esp_dev_name_cache = esp_trie_create();
		if (esp_dev_name_cache != NULL) {
			esp_register_thread_exit_action(cleanup_dev_name_cache,
							NULL);
		}
	}
	if (esp_dev_name_cache != NULL) {
		(void) esp_trie_lookup_id_or_insert_ex(esp_dev_name_cache,
						       dev_name, &dev_id,
						       esp_alloc_shared_name);
	}
	return dev_id;
}

/* Initialize ESP profiling support for libfbaric EFA provider. */
void esp_init()
{
	/* Initialize ESP library. */
	EFA_INFO(FI_LOG_CORE, "Initializing ESP for libfbaric\n");
	int res = esp_initialize();
	if (res != 0) {
		if (res == ESP_ERROR_RANK_DISABLED) {
			EFA_INFO(FI_LOG_CORE,
				 "Profiling for current rank %d is "
				 "disabled by user configuration, no profiling "
				 "data will be collected for this rank\n",
				 esp_get_rank_id());
		} else {
			EFA_WARN(FI_LOG_CORE,
				 "Failed to initialize ESP profiling library, "
				 "error code: %d\n",
				 res);
		}
		return;
	}
	esp_current_rank_enabled = 1;

	/* NOTE: Since libfabric does not provide orderly termination hook
	 * (provider cleanup hook is called from fi_fini () during library
	 * termination, way too late after C-runtime library executes tear down
	 * code and aborts due to running threads), it is required by upper
	 * layer library to initialize/terminate the ESP library. */
	atexit(esp_finalize);
	EFA_INFO(FI_LOG_CORE,
		 "Regsitered atexit handler for ESP library teardown\n");

	/* Load FI_ESP_ENABLE_COUNTER_DATA env var. */
	esp_enable_counter_data = esp_load_env("FI_ESP_ENABLE_COUNTER_DATA");

	/* Load FI_ESP_ENABLE_PER_DEVICE_DATA env var. */
	esp_enable_per_device_data =
		esp_load_env("FI_ESP_ENABLE_PER_DEVICE_DATA");

	/* Load FI_ESP_ENABLE_BW_DATA env var. */
	esp_enable_bw_data = esp_load_env("FI_ESP_ENABLE_BW_DATA");

	/* Load FI_ESP_ENABLE_DOOR_BELL_DATA env var. */
	esp_enable_door_bell_data =
		esp_load_env("FI_ESP_ENABLE_DOOR_BELL_DATA");

	/* Load FI_ESP_ENABLE_POLL_DATA env var. */
	esp_enable_poll_data = esp_load_env("FI_ESP_ENABLE_POLL_DATA");

	/* Load FI_ESP_ENABLE_RECV_DATA env var. */
	esp_enable_recv_data = esp_load_env("FI_ESP_ENABLE_RECV_DATA");

	/* Load FI_ESP_ENABLE_TRACE env var. */
	esp_enable_trace = esp_load_env("FI_ESP_ENABLE_TRACE");

	/* Initialize bins for latency bin generator. */
	init_bin_bounds();

	/* Initialize profiling objects. */
	if (esp_enable_per_device_data) {
		init_per_device_wqe_metrics();
	} else {
		init_wqe_metrics();
	}

	/* Initialize traces. */
	if (esp_enable_trace) {
		if (esp_init_traces() != 0) {
			EFA_WARN(FI_LOG_CORE,
				 "Failed to execute ESP trace registration, "
				 "ESP traces will be disabled for libfabric\n");
			esp_enable_trace = 0;
		}
	}
}

/* Terminate ESP profiling support for libfbaric EFA provider. */
void esp_finalize()
{
	/* NOTE: this call must be idempotent, since it is also registered as
	 * atexit handler. */
	if (esp_current_rank_enabled) {
		if (esp_enable_per_device_data) {
			term_per_device_wqe_metrics();
		}
		/* NOTE: global counters and histograms are destroyed by ESP. */
		EFA_INFO(FI_LOG_CORE, "Terminating ESP for libfbaric\n");
		esp_terminate();
	}
	esp_enable_per_device_data = 0;
	esp_current_rank_enabled = 0;
}

/* Helper: create histogram by qp. */
static esp_global_histogram_t
create_histogram_for_qp(struct efa_qp *qp, const char *base_name,
			enum efa_io_send_op_type op_type,
			esp_bin_generator_t *bin_generator, const char *units,
			int is_latency)
{
	struct ibv_context *ctx = qp->base_ep->domain->device->ibv_ctx;
	const char *dev_name = ibv_get_device_name(ctx->device); // "rdmap87s0"
	const size_t NAME_LEN = 64;
	char name[NAME_LEN];
	snprintf(name, NAME_LEN, "%s[%s][%s]", base_name, op_names[op_type],
		 dev_name);
	return esp_get_global_histogram(name, bin_generator, is_latency, 1,
					units, 1);
}

/* Helper: create counter by qp. */
static esp_level_counter_t
create_counter_for_qp(struct efa_qp *qp, const char *base_name,
		      enum efa_io_send_op_type op_type,
		      esp_level_counter_type_t counter_type, const char *units,
		      uint64_t factor)
{
	struct ibv_context *ctx = qp->base_ep->domain->device->ibv_ctx;
	const char *dev_name = ibv_get_device_name(ctx->device); // "rdmap87s0"
	const size_t NAME_LEN = 64;
	char name[NAME_LEN];
	snprintf(name, NAME_LEN, "%s[%s][%s]", base_name, op_names[op_type],
		 dev_name);
	return esp_get_level_counter(name, counter_type, units, factor);
}

/* Helper: initialize histogram by qp. */
static void init_histogram_for_qp(esp_global_histogram_t *histogram,
				  struct efa_qp *qp, const char *base_name,
				  enum efa_io_send_op_type op_type,
				  esp_bin_generator_t *bin_generator,
				  const char *units, int is_latency)
{
	*histogram = create_histogram_for_qp(qp, base_name, op_type,
					     bin_generator, units, is_latency);
	if (*histogram == NULL) {
		*histogram = (esp_global_histogram_t) -1;
	}
}

/* Helper: initialize counter by qp. */
static void init_counter_for_qp(esp_level_counter_t *counter, struct efa_qp *qp,
				const char *base_name,
				enum efa_io_send_op_type op_type,
				esp_level_counter_type_t counter_type,
				const char *units, uint64_t factor)
{
	*counter = create_counter_for_qp(qp, base_name, op_type, counter_type,
					 units, factor);
	if (*counter == NULL) {
		*counter = (esp_level_counter_t) -1;
	}
}

/* Helper: reutrn NULL on failed initialization sentinel pointer. */
#define VALID_OBJECT(type, obj) ((obj == (type) - 1) ? NULL : obj)

static esp_global_histogram_t
get_wqe64_latency_histogram(enum efa_io_send_op_type op_type, struct efa_qp *qp)
{
	size_t dev_id =
		(qp->base_ep->domain->device - g_efa_selected_device_list);
	if (wqe_metrics[op_type].wqe64_latency_histograms[dev_id] == NULL) {
		init_histogram_for_qp(
			&wqe_metrics[op_type].wqe64_latency_histograms[dev_id],
			qp, "wqe64_latency", op_type, &latency_bin_generator,
			"ns", 1);
	}

	return VALID_OBJECT(
		esp_global_histogram_t,
		wqe_metrics[op_type].wqe64_latency_histograms[dev_id]);
}

static esp_global_histogram_t
get_wqe_latency_histogram(enum efa_io_send_op_type op_type, struct efa_qp *qp)
{
	size_t dev_id =
		(qp->base_ep->domain->device - g_efa_selected_device_list);
	if (wqe_metrics[op_type].wqe_latency_histograms[dev_id] == NULL) {
		init_histogram_for_qp(
			&wqe_metrics[op_type].wqe_latency_histograms[dev_id],
			qp, "wqe_latency", op_type, &latency_bin_generator,
			"ns", 1);
	}

	return VALID_OBJECT(
		esp_global_histogram_t,
		wqe_metrics[op_type].wqe_latency_histograms[dev_id]);
}

static esp_global_histogram_t
get_wqe_size_histogram(enum efa_io_send_op_type op_type, struct efa_qp *qp)
{
	size_t dev_id =
		(qp->base_ep->domain->device - g_efa_selected_device_list);
	if (wqe_metrics[op_type].wqe_size_histograms[dev_id] == NULL) {
		init_histogram_for_qp(
			&wqe_metrics[op_type].wqe_size_histograms[dev_id], qp,
			"wqe_size", op_type, ESP_LOG2_BIN_GENERATOR(), "", 0);
	}

	return VALID_OBJECT(esp_global_histogram_t,
			    wqe_metrics[op_type].wqe_size_histograms[dev_id]);
}

static esp_level_counter_t
get_wqe_inflight_reqs_counter(enum efa_io_send_op_type op_type,
			      struct efa_qp *qp)
{
	size_t dev_id =
		(qp->base_ep->domain->device - g_efa_selected_device_list);
	if (wqe_metrics[op_type].wqe_inflight_reqs_counters[dev_id] == NULL) {
		init_counter_for_qp(
			&wqe_metrics[op_type]
				 .wqe_inflight_reqs_counters[dev_id],
			qp, "wqe_inflight_reqs", op_type, ESP_COUNTING_COUNTER,
			"", 1);
	}
	return VALID_OBJECT(
		esp_level_counter_t,
		wqe_metrics[op_type].wqe_inflight_reqs_counters[dev_id]);
}

static esp_level_counter_t
get_wqe_inflight_bytes_counter(enum efa_io_send_op_type op_type,
			       struct efa_qp *qp)
{
	size_t dev_id =
		(qp->base_ep->domain->device - g_efa_selected_device_list);
	if (wqe_metrics[op_type].wqe_inflight_bytes_counters[dev_id] == NULL) {
		init_counter_for_qp(
			&wqe_metrics[op_type]
				 .wqe_inflight_bytes_counters[dev_id],
			qp, "wqe_inflight_bytes", op_type, ESP_COUNTING_COUNTER,
			"", 1);
	}
	return VALID_OBJECT(
		esp_level_counter_t,
		wqe_metrics[op_type].wqe_inflight_bytes_counters[dev_id]);
}

static esp_level_counter_t
get_wqe_estimated_bw_counter(enum efa_io_send_op_type op_type,
			     struct efa_qp *qp)
{
	size_t dev_id =
		(qp->base_ep->domain->device - g_efa_selected_device_list);
	if (wqe_metrics[op_type].wqe_estimated_bw_counters[dev_id] == NULL) {
		init_counter_for_qp(
			&wqe_metrics[op_type].wqe_estimated_bw_counters[dev_id],
			qp, "wqe_estimated_bw", op_type, ESP_COUNTING_COUNTER,
			"Gbps", 1);
	}
	return VALID_OBJECT(
		esp_level_counter_t,
		wqe_metrics[op_type].wqe_estimated_bw_counters[dev_id]);
}

#define TRACE_DATA_PATH_DIRECT(dev_name_val, src_qp_num_val, dst_qp_num_val,   \
			       ah_num_val, length_val, wr_idx_val, dev_id_val) \
	ESP_TRACE_PARENT_MEMBER(data_path_direct_base, dev_name,               \
				get_dev_name_id(dev_name_val));                \
	ESP_TRACE_PARENT_MEMBER(data_path_direct_base, src_qp_num,             \
				src_qp_num_val);                               \
	ESP_TRACE_PARENT_MEMBER(data_path_direct_base, dst_qp_num,             \
				dst_qp_num_val);                               \
	ESP_TRACE_PARENT_MEMBER(data_path_direct_base, ah_num, ah_num_val);    \
	ESP_TRACE_PARENT_MEMBER(data_path_direct_base, length, length_val);    \
	ESP_TRACE_PARENT_MEMBER(data_path_direct_base, wr_idx, wr_idx_val);    \
	ESP_TRACE_PARENT_MEMBER(data_path_direct_base, dev_id, dev_id_val);

/* Intercept WQE posted. */
void efa_data_path_direct_tracepoint_post_send_esp(
	struct efa_qp *qp, struct efa_data_path_direct_sq *sq,
	struct efa_io_tx_wqe *wqe)
{
	uint64_t wrid = 0;
	uint64_t wr_idx = 0;
	struct efa_io_tx_meta_desc *md = &wqe->meta;

	if (sq->wq.req_id_64_bit) {
		/* 64-bit mode: wr_id is encoded directly in req_id + req_id_ex
		 */
		wrid = (uint64_t) md->req_id |
		       (uint64_t) md->req_id_ex.w[0] << 16 |
		       (uint64_t) md->req_id_ex.w[1] << 32 |
		       (uint64_t) md->req_id_ex.w[2] << 48;
	} else {
		/* Legacy mode: req_id is a wrid-table index tagged with QP
		 * generation */
		if (sq->wq.wrid == NULL) {
			/* No context array, skip report. */
			return;
		}
		wr_idx = md->req_id & ~sq->wq.gen_mask;
		wrid = sq->wq.wrid[wr_idx];
	}

	if (wrid == 0) {
		/* No context, skip report */
		return;
	}
	struct efa_context *ctx = (struct efa_context *) wrid;

	/* Get WQE length. */
	uint8_t op_type =
		EFA_GET(&wqe->meta.ctrl1, EFA_IO_TX_META_DESC_OP_TYPE);
	unsigned length =
		efa_get_wqe_length((const struct efa_io_tx_wqe_128 *) wqe);

	ESP_BEGIN_BATCH_REPORT()

	ctx->start_ticks = ESP_CURR_TICK_COUNT;
	ctx->length = length;

	/* Update counters and histograms. */
	if (esp_enable_per_device_data) {
		/* Update inflight counters. */
		if (esp_enable_counter_data) {
			esp_level_counter_t counter =
				get_wqe_inflight_reqs_counter(op_type, qp);
			if (counter != NULL) {
				esp_report_counter_increase(counter, 1,
							    ESP_CURR_TIME);
			}
			counter = get_wqe_inflight_bytes_counter(op_type, qp);
			if (counter != NULL) {
				esp_report_counter_increase(counter, length,
							    ESP_CURR_TIME);
			}
		}

		/* Update size histogram. */
		esp_global_histogram_t histogram =
			get_wqe_size_histogram(op_type, qp);
		if (histogram != NULL) {
			esp_add_global_histogram_sample(histogram, length);
		}
	} else {
		/* Update inflight counters. */
		if (esp_enable_counter_data) {
			if (wqe_inflight_reqs_counter != NULL) {
				esp_report_counter_increase(
					wqe_inflight_reqs_counter, 1,
					ESP_CURR_TIME);
			}
			if (wqe_inflight_bytes_counter != NULL) {
				esp_report_counter_increase(
					wqe_inflight_bytes_counter, length,
					ESP_CURR_TIME);
			}
		}

		/* Update size histogram. */
		if (wqe_size_histogram != NULL) {
			esp_add_global_histogram_sample(wqe_size_histogram,
							length);
		}
	}

	// TODO: fix this (probably nccl ctx is null, why?)
	/* Issue trace record if needed. */
	if (esp_enable_trace && esp_nccl_should_trace_current_iteration()) {
		const char *dev_name =
			qp->base_ep->domain->device->ibv_ctx->device->name;
		uint32_t dev_id = (uint32_t) (qp->base_ep->domain->device -
					      g_efa_selected_device_list);
		ESP_BEGIN_TRACE_TIME(data_path_direct_post_send, ESP_CURR_TIME);
		TRACE_DATA_PATH_DIRECT(dev_name, qp->ibv_qp->qp_num,
				       wqe->meta.dest_qp_num, wqe->meta.ah,
				       length, wr_idx, dev_id);
		ESP_TRACE_MEMBER(op_type, op_type_name_ids[op_type]);
		ESP_TRACE_MEMBER(wr_id, wrid);
		ESP_END_TRACE();
	}

	ESP_END_BATCH_REPORT();
}

/* Intercept WQE completed. */
extern void efa_data_path_direct_tracepoint_process_completion_esp(
	struct efa_qp *qp, struct ibv_cq_ex *ibvcqx,
	struct efa_io_cdesc_common *cqe)
{
	int opcode;
	uint32_t src_qp_num;
	uint16_t ah_num;
	uint32_t length = 0;
	uint16_t wr_idx = cqe->req_id;
	uint64_t wrid = ibvcqx->wr_id;

	/* Get efa context. */
	if (wrid == 0) {
		/* No context, skip report */
		return;
	}
	struct efa_context *ctx = ((struct efa_context *) wrid);

	/* Get saved start ticks and length for this wqe. */
	uint64_t start_ticks = ctx->start_ticks;
	if (start_ticks == 0) {
		/* No start ticks set, skip. */
		return;
	}

	/* Extract opcode inline - similar to
	 * efa_data_path_direct_wc_read_opcode */
	enum efa_io_send_op_type op_type =
		EFA_GET(&cqe->flags, EFA_IO_CDESC_COMMON_OP_TYPE);

	/* Get operation attributes. */
	if (EFA_GET(&cqe->flags, EFA_IO_CDESC_COMMON_Q_TYPE) ==
	    EFA_IO_SEND_QUEUE) {
		opcode = (op_type == EFA_IO_RDMA_WRITE) ? IBV_WC_RDMA_WRITE :
							  IBV_WC_SEND;
		src_qp_num = qp->ibv_qp->qp_num; /* For TX, src is our QP */
		ah_num = UINT16_MAX; /* Not applicable for TX */
	} else {
		/* RX completion */
		opcode = (op_type == EFA_IO_RDMA_WRITE) ?
				 IBV_WC_RECV_RDMA_WITH_IMM :
				 IBV_WC_RECV;
		/* Extract src_qp and ah from RX completion - inline version of
		 * helper functions */
		const struct efa_io_rx_cdesc *rcqe =
			container_of(cqe, struct efa_io_rx_cdesc, common);
		src_qp_num = rcqe->src_qp_num;
		ah_num = rcqe->ah;

		/* Extract length for RX - inline version of
		 * efa_data_path_direct_wc_read_byte_len */
		const struct efa_io_rx_cdesc_ex *rcqe_ex = container_of(
			cqe, struct efa_io_rx_cdesc_ex, base.common);
		length = rcqe_ex->base.length;
		if (op_type == EFA_IO_RDMA_WRITE)
			length |= ((uint32_t) rcqe_ex->u.rdma_write.length_hi
				   << 16);

		/* Extract wr_idx. */
		wr_idx = rcqe->common.req_id;
	}

	ESP_BEGIN_BATCH_REPORT()
	length = ctx->length;

	/* Compute tick diff. */
	uint64_t tick_diff = ESP_CURR_TICK_COUNT - start_ticks;
	ctx->start_ticks = 0;
	if (tick_diff > 100000000) {
		// throw away anything above 100 millis (why do we get those?)
		return;
	}

	/* Update counters and histograms. */
	if (esp_enable_per_device_data) {
		/* Update inflight counters. */
		if (esp_enable_counter_data) {
			esp_level_counter_t counter =
				get_wqe_inflight_reqs_counter(op_type, qp);
			if (counter != NULL) {
				esp_report_counter_decrease(counter, 1,
							    ESP_CURR_TIME);
			}
			counter = get_wqe_inflight_bytes_counter(op_type, qp);
			if (counter != NULL) {
				esp_report_counter_decrease(counter, length,
							    ESP_CURR_TIME);
			}
		}

		/* Update latency histograms. */
		if (length == 64) {
			esp_global_histogram_t histogram =
				get_wqe64_latency_histogram(op_type, qp);
			if (histogram != NULL) {
				esp_add_global_histogram_sample(histogram,
								tick_diff);
			}
		} else {
			esp_global_histogram_t histogram =
				get_wqe_latency_histogram(op_type, qp);
			if (histogram != NULL) {
				esp_add_global_histogram_sample(histogram,
								tick_diff);
			}
		}
	} else {
		/* Update inflight counters. */
		if (esp_enable_counter_data) {
			if (wqe_inflight_reqs_counter != NULL) {
				esp_report_counter_decrease(
					wqe_inflight_reqs_counter, 1,
					ESP_CURR_TIME);
			}
			if (wqe_inflight_bytes_counter != NULL) {
				esp_report_counter_decrease(
					wqe_inflight_bytes_counter, length,
					ESP_CURR_TIME);
			}
		}

		/* Update latency histograms. */
		if (length == 64) {
			if (wqe64_latency_histogram != NULL) {
				esp_add_global_histogram_sample(
					wqe64_latency_histogram, tick_diff);
			}
		} else {
			if (wqe_latency_histogram != NULL) {
				esp_add_global_histogram_sample(
					wqe_latency_histogram, tick_diff);
			}
		}
	}

	/* Issue trace record if needed. */
	if (esp_enable_bw_data) {
		/* Apply Little's law to estimate the current BW:
		 * BW = Queue-Depth X Payload-Size / WQE-Latency */
		uint64_t queue_depth = 0;
		esp_level_counter_t counter =
			get_wqe_inflight_reqs_counter(op_type, qp);
		if (counter != NULL) {
			esp_get_counter_level(counter, &queue_depth);
		}
		if (queue_depth > 0) {
			/* Assuming steady state payload size. */
			uint64_t payload_bytes = length;
			uint64_t wqe_latency_ns =
				esp_wall_clock_to_nanos(tick_diff);
			if (wqe_latency_ns > 0) {
				uint64_t estimated_bw = queue_depth *
							payload_bytes /
							wqe_latency_ns;
				/* This is in byte/ns which is equivalent to
				 * GiB/second, we only need to convert to Gbps.
				 */
				estimated_bw *= 8;

				if (esp_enable_per_device_data) {
					counter = get_wqe_estimated_bw_counter(
						op_type, qp);
					if (counter != NULL) {
						esp_report_counter_level(
							counter, estimated_bw,
							ESP_CURR_TIME);
					}
				} else {
					if (wqe_estimated_bw_counter != NULL) {
						esp_report_counter_level(
							wqe_estimated_bw_counter,
							estimated_bw,
							ESP_CURR_TIME);
					}
				}
			}
		}
	}

	/* Issue trace record if needed. */
	if (esp_enable_trace && esp_nccl_should_trace_current_iteration()) {
		const char *dev_name =
			qp->base_ep->domain->device->ibv_ctx->device->name;
		uint32_t dev_id = (uint32_t) (qp->base_ep->domain->device -
					      g_efa_selected_device_list);
		ESP_BEGIN_TRACE_TIME(data_path_direct_process_completion,
				     ESP_CURR_TIME);
		TRACE_DATA_PATH_DIRECT(dev_name, src_qp_num, qp->ibv_qp->qp_num,
				       ah_num, length, wr_idx, dev_id);
		ESP_TRACE_MEMBER(ibvcqx, ibvcqx);
		ESP_TRACE_MEMBER(opcode, opcode);
		ESP_END_TRACE();
	}

	ESP_END_BATCH_REPORT();
}

void efa_data_path_direct_send_wr_ring_db_start_esp(
	struct efa_data_path_direct_sq *sq)
{
	if (esp_enable_door_bell_data) {
		ESP_BEGIN_BATCH_REPORT();

		/* Initialize histogram on-demand for current thread. */
		if (efa_data_path_direct_send_wr_ring_db_latency ==
		    ESP_THREAD_LOCAL_VAR_REQUIRES_INIT) {
			efa_data_path_direct_send_wr_ring_db_latency =
				esp_get_thread_histogram(
					"efa_data_path_direct_send_wr_ring_db_"
					"latency",
					ESP_LINEAR_BIN_GENERATOR(50, 10, 0), 1,
					1, "ns", 1);
		}

		/* Add start sample. */
		if (efa_data_path_direct_send_wr_ring_db_latency != NULL) {
			esp_add_histogram_sample_start(
				efa_data_path_direct_send_wr_ring_db_latency,
				ESP_CURR_TICK_COUNT);
		}

		/* Add wqu batch size sample. */
		if (wqe_batch_size_histogram != NULL) {
			esp_add_global_histogram_sample(
				wqe_batch_size_histogram, sq->num_wqe_pending);
		}

		ESP_END_BATCH_REPORT();
	}
}

void efa_data_path_direct_send_wr_ring_db_end_esp(
	struct efa_data_path_direct_sq *sq)
{
	if (esp_enable_door_bell_data) {
		/* Add end sample for ring doorbell. */
		(void) sq;
		if (efa_data_path_direct_send_wr_ring_db_latency != NULL) {
			esp_add_histogram_sample_end(
				efa_data_path_direct_send_wr_ring_db_latency,
				esp_get_wall_clock_ticks());
		}
	}
}

static esp_histogram_t get_efa_cq_readfrom_host_histogram()
{
	/* Initialize histogram on-demand for current thread. */
	if (efa_cq_readfrom_host_histogram ==
	    ESP_THREAD_LOCAL_VAR_REQUIRES_INIT) {
		efa_cq_readfrom_host_histogram = esp_get_thread_histogram(
			"efa_cq_readfrom_host_latency",
			ESP_LINEAR_BIN_GENERATOR(50, 10, 0), 1, 1, "ns", 1);
	}
	return efa_cq_readfrom_host_histogram;
}

static esp_histogram_t get_efa_cq_readfrom_device_histogram()
{
	/* Initialize histogram on-demand for current thread. */
	if (efa_cq_readfrom_device_histogram ==
	    ESP_THREAD_LOCAL_VAR_REQUIRES_INIT) {
		efa_cq_readfrom_device_histogram = esp_get_thread_histogram(
			"efa_cq_readfrom_device_latency",
			ESP_LINEAR_BIN_GENERATOR(50, 10, 0), 1, 1, "ns", 1);
	}
	return efa_cq_readfrom_device_histogram;
}

void efa_cq_readfrom_start_host_esp()
{
	if (esp_enable_poll_data) {
		esp_histogram_t histogram =
			get_efa_cq_readfrom_host_histogram();
		if (histogram != NULL) {
			esp_add_histogram_sample_start(
				histogram, esp_get_wall_clock_ticks());
		}
	}
}

void efa_cq_readfrom_end_host_esp(size_t num_cqe)
{
	if (esp_enable_poll_data) {
		esp_histogram_t histogram =
			get_efa_cq_readfrom_host_histogram();
		if (histogram != NULL) {
			esp_add_histogram_sample_end(
				histogram, esp_get_wall_clock_ticks());
		}
		if (efa_cq_readfrom_count != NULL) {
			esp_add_global_histogram_sample(efa_cq_readfrom_count,
							num_cqe);
		}
	}
}

void efa_cq_readfrom_start_device_esp()
{
	if (esp_enable_poll_data) {
		esp_histogram_t histogram =
			get_efa_cq_readfrom_device_histogram();
		if (histogram != NULL) {
			esp_add_histogram_sample_start(
				histogram, esp_get_wall_clock_ticks());
		}
	}
}

void efa_cq_readfrom_end_device_esp()
{
	if (esp_enable_poll_data) {
		esp_histogram_t histogram =
			get_efa_cq_readfrom_device_histogram();
		if (histogram != NULL) {
			esp_add_histogram_sample_end(
				histogram, esp_get_wall_clock_ticks());
		}
	}
}

void efa_data_path_direct_tracepoint_post_recv_esp(struct efa_qp *qp,
						   struct ibv_recv_wr *wr)
{
	if (esp_enable_recv_data) {
		/* Issue trace record*/
		ESP_BEGIN_TRACE(data_path_direct_post_recv);
		ESP_TRACE_MEMBER(
			dev_name,
			get_dev_name_id(qp->base_ep->domain->device->ibv_ctx
						->device->name));
		ESP_TRACE_MEMBER(wr_id, wr->wr_id);
		ESP_TRACE_MEMBER(qp_num, qp->ibv_qp->qp_num);
		ESP_TRACE_MEMBER(num_sge, wr->num_sge);
		ESP_END_TRACE();
	}
}

#endif
