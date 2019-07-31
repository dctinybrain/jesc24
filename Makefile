# Build Coq sources according to `_CoqProject`.

COQ_MAKEFILE := coq_makefile
REDIR := $(MAKE) -f Makefile.coq

all: Makefile.coq
	+@$(REDIR) $@
.PHONY: all

cleanall: Makefile.coq
	+@$(REDIR) $@
	@echo CLEAN Makefile.coq Makefile.coq.conf
	@rm -f Makefile.coq Makefile.coq.conf
.PHONY: cleanall

# Enable $(REDIR)
Makefile.coq Makefile.coq.conf: _CoqProject Makefile
	+@echo COQ_MAKEFILE
	+@$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq

# $(REDIR)
%: Makefile.coq
	+@$(REDIR) $@

# Don't $(REDIR)
Makefile _CoqProject: ;
