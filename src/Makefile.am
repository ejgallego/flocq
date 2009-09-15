FILES = \
	Flocq_defs.v \
	Flocq_float_prop.v \
	Flocq_Raux.v \
	Flocq_rnd_ex.v \
	Flocq_rnd_FIX.v \
	Flocq_rnd_FLT.v \
	Flocq_rnd_FLX.v \
	Flocq_rnd_generic.v \
	Flocq_rnd_ne.v \
	Flocq_rnd_prop.v \
	Flocq_ulp.v

data_DATA = $(FILES:=o)
EXTRA_DIST = $(FILES)
CLEANFILES = $(FILES:=o) $(FILES:=d) $(FILES:.v=.glob)

datadir = $(libdir)

.v.vo:
	@echo COQC $<
	@$(COQC) $(COQRFLAG) -dont-load-proofs $<

.v.vd:
	@echo COQDEP $<
	@$(COQDEP) -I . $< > $@

SUFFIXES = .v .vo .vd

-include $(FILES:=d)
