(*
  file:     mat_map.v
  purpose:  zero matrix and unit matrix.
*)


From Digital Require Export Mat_def.


(** ** zero matrix *)
Section matzero.
  
  Variable A : Type.
  Variable A0 A1 : A.
  
  Definition matzero {r c} := mk_mat (dlzero A0 r c)
    (dlzero_height A0) (dlzero_width A0).
  
  Definition matunit {n} := mk_mat (dlunit A0 A1 n)
    (dlunit_height A0 A1) (dlunit_width A0 A1).

End matzero.

Arguments matzero {A}.
Arguments matunit {A}.