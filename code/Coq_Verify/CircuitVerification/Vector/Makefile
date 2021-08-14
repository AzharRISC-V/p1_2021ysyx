
COQC = coqc
COQCFLAGS = -Q ../ Digital

all : List_aux.vo Mat_def.vo Mat_map.vo Mat_IO.vo Mat_add.vo Mat_sub.vo \
	Mat_trans.vo Mat_mul.vo

List_aux.vo : List_aux.v
	$(COQC) $(COQCFLAGS) $<
Mat_def.vo : Mat_def.v List_aux.vo
	$(COQC) $(COQCFLAGS) $<
Mat_map.vo : Mat_map.v Mat_def.vo
	$(COQC) $(COQCFLAGS) $<
Mat_IO.vo : Mat_IO.v Mat_def.vo
	$(COQC) $(COQCFLAGS) $<
Mat_add.vo : Mat_add.v Mat_IO.v Mat_map.vo
	$(COQC) $(COQCFLAGS) $<
Mat_sub.vo : Mat_sub.v Mat_IO.v Mat_map.vo
	$(COQC) $(COQCFLAGS) $<
Mat_trans.vo : Mat_trans.v Mat_IO.v Mat_map.vo
	$(COQC) $(COQCFLAGS) $<
Mat_mul.vo : Mat_mul.v Mat_trans.vo Mat_add.vo Mat_sub.vo
	$(COQC) $(COQCFLAGS) $<

.PHONY : clean

clean :
	rm -f *.vo *.glob *.vos *.vok .*.aux *.mli *.ml