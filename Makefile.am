FILES = \
	Flocq_Raux.v \
	Flocq_defs.v \
	Flocq_rnd_ex.v

data_DATA = $(FILES:=o)
EXTRA_DIST = autogen.sh $(FILES)
CLEANFILES = $(FILES:=o) $(FILES:=d)

datadir = $(libdir)

%.vo: %.v
	@echo COQC $<
	@$(COQC) $(COQRFLAG) $<

%.vd: %.v
	@echo COQDEP $<
	@$(COQDEP) $< | sed -e 's,\($*\)\.vo[ :]*,\1.vo $@ : ,g' > $@

include $(FILES:=d)
