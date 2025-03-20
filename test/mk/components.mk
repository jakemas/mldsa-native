# SPDX-License-Identifier: Apache-2.0

FIPS202_SRCS = $(wildcard mldsa/fips202/*.c)
SOURCES += $(wildcard mldsa/*.c)

ALL_TESTS = test_mldsa acvp_mldsa bench_mldsa bench_components_mldsa gen_NISTKAT gen_KAT
NON_NIST_TESTS = $(filter-out gen_NISTKAT,$(ALL_TESTS))

MLDSA44_DIR = $(BUILD_DIR)/mldsa44
MLDSA65_DIR = $(BUILD_DIR)/mldsa65
MLDSA87_DIR = $(BUILD_DIR)/mldsa87

MLDSA44_OBJS = $(call MAKE_OBJS,$(MLDSA44_DIR),$(SOURCES) $(FIPS202_SRCS))
$(MLDSA44_OBJS): CFLAGS += -DMLD_MODE=2
MLDSA65_OBJS = $(call MAKE_OBJS,$(MLDSA65_DIR),$(SOURCES) $(FIPS202_SRCS))
$(MLDSA65_OBJS): CFLAGS += -DMLD_MODE=3
MLDSA87_OBJS = $(call MAKE_OBJS,$(MLDSA87_DIR),$(SOURCES) $(FIPS202_SRCS))
$(MLDSA87_OBJS): CFLAGS += -DMLD_MODE=5

$(BUILD_DIR)/libmldsa44.a: $(MLDSA44_OBJS)
$(BUILD_DIR)/libmldsa65.a: $(MLDSA65_OBJS)
$(BUILD_DIR)/libmldsa87.a: $(MLDSA87_OBJS)

$(BUILD_DIR)/libmldsa.a: $(MLDSA44_OBJS) $(MLDSA65_OBJS) $(MLDSA87_OBJS)

$(MLDSA44_DIR)/bin/bench_mldsa44: CFLAGS += -Itest/hal
$(MLDSA65_DIR)/bin/bench_mldsa65: CFLAGS += -Itest/hal
$(MLDSA87_DIR)/bin/bench_mldsa87: CFLAGS += -Itest/hal
$(MLDSA44_DIR)/bin/bench_components_mldsa44: CFLAGS += -Itest/hal
$(MLDSA65_DIR)/bin/bench_components_mldsa65: CFLAGS += -Itest/hal
$(MLDSA87_DIR)/bin/bench_components_mldsa87: CFLAGS += -Itest/hal

$(MLDSA44_DIR)/bin/bench_mldsa44: $(MLDSA44_DIR)/test/hal/hal.c.o
$(MLDSA65_DIR)/bin/bench_mldsa65: $(MLDSA65_DIR)/test/hal/hal.c.o
$(MLDSA87_DIR)/bin/bench_mldsa87: $(MLDSA87_DIR)/test/hal/hal.c.o
$(MLDSA44_DIR)/bin/bench_components_mldsa44: $(MLDSA44_DIR)/test/hal/hal.c.o
$(MLDSA65_DIR)/bin/bench_components_mldsa65: $(MLDSA65_DIR)/test/hal/hal.c.o
$(MLDSA87_DIR)/bin/bench_components_mldsa87: $(MLDSA87_DIR)/test/hal/hal.c.o

$(MLDSA44_DIR)/bin/%: CFLAGS += -DMLD_MODE=2
$(MLDSA65_DIR)/bin/%: CFLAGS += -DMLD_MODE=3
$(MLDSA87_DIR)/bin/%: CFLAGS += -DMLD_MODE=5

# Link tests with respective library
define ADD_SOURCE
$(BUILD_DIR)/$(1)/bin/$(2)$(shell echo $(1) | tr -d -c 0-9): LDLIBS += -L$(BUILD_DIR) -l$(1)
$(BUILD_DIR)/$(1)/bin/$(2)$(shell echo $(1) | tr -d -c 0-9): $(BUILD_DIR)/$(1)/test/$(2).c.o $(BUILD_DIR)/lib$(1).a
endef

$(foreach scheme,mldsa44 mldsa65 mldsa87, \
	$(foreach test,$(ALL_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test))) \
	) \
)

# nistkat tests require special RNG
$(MLDSA44_DIR)/bin/gen_NISTKAT44: CFLAGS += -Itest/nistrng
$(MLDSA44_DIR)/bin/gen_NISTKAT44: $(call MAKE_OBJS, $(MLDSA44_DIR), $(wildcard test/nistrng/*.c))
$(MLDSA65_DIR)/bin/gen_NISTKAT65: CFLAGS += -Itest/nistrng
$(MLDSA65_DIR)/bin/gen_NISTKAT65: $(call MAKE_OBJS, $(MLDSA65_DIR), $(wildcard test/nistrng/*.c))
$(MLDSA87_DIR)/bin/gen_NISTKAT87: CFLAGS += -Itest/nistrng
$(MLDSA87_DIR)/bin/gen_NISTKAT87: $(call MAKE_OBJS, $(MLDSA87_DIR), $(wildcard test/nistrng/*.c))

# All other tests use test-only RNG
$(NON_NIST_TESTS:%=$(MLDSA44_DIR)/bin/%44): $(call MAKE_OBJS, $(MLDSA44_DIR), $(wildcard test/notrandombytes/*.c))
$(NON_NIST_TESTS:%=$(MLDSA65_DIR)/bin/%65): $(call MAKE_OBJS, $(MLDSA65_DIR), $(wildcard test/notrandombytes/*.c))
$(NON_NIST_TESTS:%=$(MLDSA87_DIR)/bin/%87): $(call MAKE_OBJS, $(MLDSA87_DIR), $(wildcard test/notrandombytes/*.c))
