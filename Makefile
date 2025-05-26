# Standard Makefile for Coq projects, relying on coq_makefile

BIN_DIR_NAME= bin

all: init Makefile.coq
	@+$(MAKE) -f Makefile.coq all
	
init: 
	@if [ -d "$(BIN_DIR_NAME)" ]; then \
		echo "$(BIN_DIR_NAME)/ directory already exits."; \
	else \
		mkdir $(BIN_DIR_NAME); \
		echo "$(BIN_DIR_NAME)/ directory has been created."; \
	fi

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -vf Makefile.coq Makefile.coq.conf
	@rm -rvf $(BIN_DIR_NAME)

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all  init clean force
