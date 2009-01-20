FILES = \
	Flocq_Raux.v \
	Flocq_defs.v \
	Flocq_rnd_ex.v

data_DATA = $(FILES:=o)
EXTRA_DIST = $(FILES)
CLEANFILES = $(FILES:=o) $(FILES:=d)

datadir = $(libdir)

%.vo: %.v
	@echo COQC $<
	@$(COQC) $(COQRFLAG) $<

%.vd: %.v
	@echo COQDEP $<
	@$(COQDEP) $< > $@

-include $(FILES:=d)
