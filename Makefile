all: Makefile.coq
	$(MAKE) -f Makefile.coq all


install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all html clean

dummy:

%.vo: Makefile.coq dummy
	$(MAKE) -f Makefile.coq $@
