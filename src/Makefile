PKG = balanced

VARIANTS = bt1 bt2 btw1 btw2
TARGETS = $(VARIANTS:=.cmi) $(VARIANTS:=.cmo) $(VARIANTS:=.cmx)
OTHER = ../META $(VARIANTS:=.ml) $(VARIANTS:=.mli)

RUNTIME = native
TESTS = 

all:
	ocamlbuild $(TARGETS)

clean:
	ocamlbuild -clean

install: all
	cd _build && ocamlfind install $(PKG) $(OTHER) $(TARGETS)

uninstall:
	ocamlfind remove $(PKG)

reinstall:
	-$(MAKE) uninstall
	$(MAKE) install
	
check test: $(TESTS)

.PHONY: all check test install $(TESTS)

$(TESTS):
	ocamlbuild -tag debug $@
	OCAMLRUNPARAM=b ./$@
