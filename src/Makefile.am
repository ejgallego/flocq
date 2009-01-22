FILES = \
	Flocq_Raux.v \
	Flocq_defs.v \
	Flocq_rnd_ex.v

data_DATA = $(FILES:=o)
EXTRA_DIST = $(FILES)
CLEANFILES = $(FILES:=o) $(FILES:=d) $(FILES:.v=.glob)

datadir = $(libdir)

.v.vo:
	@echo COQC $<
	@$(COQC) $(COQRFLAG) $<

.v.vd:
	@echo COQDEP $<
	@$(COQDEP) -I . $< > $@

SUFFIXES = .v .vo .vd

-include $(FILES:=d)
