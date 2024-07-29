COQMODULE    := Fairness
COQTHEORIES  := \
	pico/*.v \
	src/lib/*.v \
	src/semantics/*.v \
	src/simulation/*.v \
	src/scheduler_example/*.v \
	src/ra/*.v \
	src/tlogic/*.v \
	src/example/*.v \
	src/bi/lib/*.v \
	src/example/treiber/*.v \
	src/example/elimstack/*.v \
	src/example/fos_ticketlock/*.v \
	src/iris_base_logic/base_logic/*.v \
	# src/iris_base_logic/base_logic/lib/*.v \


.PHONY: all theories clean

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq vio

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-arg -w -arg -deprecated-instance-without-locality"; \
	 echo "-arg -w -arg -ambiguous-paths"; \
	 echo "-arg -w -arg -redundant-canonical-projection"; \
	 echo "-Q src/lib $(COQMODULE)"; \
	 echo "-Q src/semantics $(COQMODULE)"; \
	 echo "-Q src/simulation $(COQMODULE)"; \
	 echo "-Q src/scheduler_example $(COQMODULE)"; \
	 echo "-Q src/ra $(COQMODULE)"; \
	 echo "-Q src/bi $(COQMODULE)"; \
	 echo "-Q src/tlogic $(COQMODULE)"; \
	 echo "-Q src/example $(COQMODULE)"; \
	 echo "-Q src/iris_base_logic $(COQMODULE)"; \
	 echo "-Q pico $(COQMODULE)"; \
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
