include ../../config.mk

TARGET = libidris2_support

LIBTARGET = $(TARGET).a
DYLIBTARGET = $(TARGET)$(SHLIB_SUFFIX)
IDRIS2_DESTDIR := ${DESTDIR}${PREFIX}

SRCS := $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)

CFLAGS += -O2

ifeq ($(OS), windows)
	SRCS += windows/win_utils.c windows/win_hack.c
	CPPFLAGS += -DWIN32_LEAN_AND_MEAN
	LDFLAGS += -lws2_32
ifeq ($(OLD_WIN), 1)
	CPPFLAGS += -D_OLD_WIN
endif
endif


all: build

.PHONY: build

build: $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET): $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

$(DYLIBTARGET): $(OBJS)
	$(CC) -shared -o $@ $^ $(LDFLAGS)


-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean:
	$(RM) $(OBJS) $(DYLIBTARGET) $(LIBTARGET)

cleandep: clean
	$(RM) $(DEPS)


.PHONY: install

install: build
	mkdir -p ${IDRIS2_DESTDIR}/idris2-${IDRIS2_VERSION}/lib
	mkdir -p ${IDRIS2_DESTDIR}/idris2-${IDRIS2_VERSION}/include
	install -m 755 $(DYLIBTARGET) ${IDRIS2_DESTDIR}/idris2-${IDRIS2_VERSION}/lib
	install -m 644 $(LIBTARGET)   ${IDRIS2_DESTDIR}/idris2-${IDRIS2_VERSION}/lib
	install -m 644 *.h            ${IDRIS2_DESTDIR}/idris2-${IDRIS2_VERSION}/include
