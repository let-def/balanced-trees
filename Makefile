TARGET = main
all: $(TARGET)

%.cmi: %.mli
	ocamlopt -g -c $<

%.cmx: %.ml
	ocamlopt -inline 30 -g -c $<

IMPLEMS = bt_1 bt_2 btw_1 btw_2  

main: $(IMPLEMS:=.cmi) $(IMPLEMS:=.cmx) main.cmx
	ocamlopt -g -o $@ $(IMPLEMS:=.cmx) main.cmx

clean:
	rm -f $(TARGET) *.cm* *.o
