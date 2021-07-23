include ../../config.mk

TARGET = libidris2_refc

ifeq ($(USE_LIBBF), 1)
	TARGET = libidris2_refc_libbf
endif

LIBTARGET = $(TARGET).a

SRCS := $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)

CFLAGS += -O2

ifeq ($(OLD_WIN), 1)
	CPPFLAGS += -D_OLD_WIN
endif

ifeq ($(USE_LIBBF), 1)
	CFLAGS += -DINTEGER_USE_LIBBF
endif


all: build

.PHONY: build

build: $(LIBTARGET)

$(LIBTARGET): $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean:
	$(RM) $(OBJS) $(LIBTARGET)

cleandep: clean
	$(RM) $(DEPS)


.PHONY: install

install: build
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/refc
	install $(LIBTARGET) *.h ${PREFIX}/idris2-${IDRIS2_VERSION}/refc
