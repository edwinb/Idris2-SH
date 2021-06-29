all:
	${IDRIS2} --build base.ipkg ${IDRIS2_FLAGS}

install:
	${IDRIS2} --install base.ipkg ${IDRIS2_FLAGS}

install-with-src:
	${IDRIS2} --install-with-src base.ipkg ${IDRIS2_FLAGS}

docs:
	${IDRIS2} --mkdoc base.ipkg

clean:
	$(RM) -r build
