COQMODULE    := Fairness
COQTHEORIES  := \
	pico/*.v \
	coq/*.v \
	src/lib/*.v \
	src/semantics/*.v \
	src/simulation/*.v \
	src/logic/*.v \
	src/example/*.v \

.PHONY: all theories clean

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq vio

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-Q src/lib $(COQMODULE)"; \
	 echo "-Q src/semantics $(COQMODULE)"; \
	 echo "-Q src/simulation $(COQMODULE)"; \
	 echo "-Q src/logic $(COQMODULE)"; \
	 echo "-Q src/example $(COQMODULE)"; \
	 echo "-Q pico $(COQMODULE)"; \
	 echo "-Q coq $(COQMODULE)"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq Makefile.coq.conf
