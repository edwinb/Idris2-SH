all:
	${IDRIS2} --build prelude.ipkg ${IDRIS2_FLAGS}

install:
	${IDRIS2} --install prelude.ipkg ${IDRIS2_FLAGS}

install-with-src:
	${IDRIS2} --install-with-src prelude.ipkg ${IDRIS2_FLAGS}

docs:
	${IDRIS2} --mkdoc prelude.ipkg

clean:
	$(RM) -r build
