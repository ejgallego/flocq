FILES = \
	Core/Fcore_defs.v \
	Core/Fcore_float_prop.v \
	Core/Fcore_Raux.v \
	Core/Fcore_rnd.v \
	Core/Fcore_FIX.v \
	Core/Fcore_FLT.v \
	Core/Fcore_FLX.v \
	Core/Fcore_FTZ.v \
	Core/Fcore_generic_fmt.v \
	Core/Fcore_rnd_ne.v \
	Core/Fcore_ulp.v \
	Core/Fcore.v \
	Calc/Fcalc_bracket.v \
	Calc/Fcalc_digits.v \
	Calc/Fcalc_div.v \
	Calc/Fcalc_ops.v \
	Prop/Fprop_nearest.v

data_DATA = $(FILES:=o)
EXTRA_DIST = $(FILES)
CLEANFILES = $(FILES:=o) $(FILES:=d) $(FILES:.v=.glob)

datadir = $(libdir)

.v.vo:
	@echo COQC $<
	@$(COQC) $(COQRFLAG) -dont-load-proofs $<

.v.vd:
	@echo COQDEP $<
	@$(COQDEP) -I Core -I Calc $< > $@

SUFFIXES = .v .vo .vd

-include $(FILES:=d)
