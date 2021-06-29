all:
	${IDRIS2} --build network.ipkg ${IDRIS2_FLAGS}

install:
	${IDRIS2} --install network.ipkg ${IDRIS2_FLAGS}

install-with-src:
	${IDRIS2} --install-with-src network.ipkg ${IDRIS2_FLAGS}

docs:
	${IDRIS2} --mkdoc network.ipkg

clean:
	$(RM) -r build
