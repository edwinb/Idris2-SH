all:
	${IDRIS2} --build test.ipkg ${IDRIS2_FLAGS}

install:
	${IDRIS2} --install test.ipkg ${IDRIS2_FLAGS}

install-with-src:
	${IDRIS2} --install-with-src test.ipkg ${IDRIS2_FLAGS}

docs:
	${IDRIS2} --mkdoc test.ipkg

clean:
	$(RM) -r build
