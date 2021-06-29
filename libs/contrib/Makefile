all:
	${IDRIS2} --build contrib.ipkg ${IDRIS2_FLAGS}

install:
	${IDRIS2} --install contrib.ipkg ${IDRIS2_FLAGS}

install-with-src:
	${IDRIS2} --install-with-src contrib.ipkg ${IDRIS2_FLAGS}

docs:
	${IDRIS2} --mkdoc contrib.ipkg

clean:
	$(RM) -r build
