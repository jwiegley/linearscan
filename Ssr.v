Require Export Ssreflect.ssreflect.
Require Export Ssreflect.ssrfun.
Require Export Ssreflect.ssrbool.
Require Export Ssreflect.eqtype.
Require Export Ssreflect.seq.
Require Export Ssreflect.ssrnat.
Require Export Ssreflect.fintype.

Extract Inductive unit    => "()" [ "()" ].
Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sum     => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive list    => "[]" ["[]" "(:)"].
Extract Inductive prod    => "(,)" ["(,)"].
Extract Inductive sigT    => "(,)" ["(,)"].
Extract Inductive option  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

Extract Inductive ordinal => "Prelude.Int" [""].

Extract Inlined Constant addn      => "(Prelude.+)".
Extract Inlined Constant andb      => "(Prelude.&&)".
Extract Inlined Constant app       => "(Prelude.++)".
Extract Inlined Constant cat       => "(Prelude.++)".
Extract Inlined Constant eqb       => "(Prelude.==)".
Extract Inlined Constant eqn       => "(Prelude.==)".
Extract Inlined Constant filter    => "Prelude.filter".
Extract Inlined Constant foldl     => "Data.List.foldl'".
Extract Inlined Constant foldr     => "Prelude.foldr".
Extract Inlined Constant fst       => "Prelude.fst".
Extract Inlined Constant has       => "Data.List.any".
Extract Inlined Constant length    => "Data.List.length".
Extract Inlined Constant leq       => "(Prelude.<=)".
Extract Inlined Constant map       => "Prelude.map".
Extract Inlined Constant maxn      => "Prelude.max".
Extract Inlined Constant minn      => "Prelude.min".
Extract Inlined Constant minus     => "(Prelude.-)".
Extract Inlined Constant mult      => "(Prelude.*)".
Extract Inlined Constant negb      => "Prelude.not".
Extract Inlined Constant orb       => "(Prelude.||)".
Extract Inlined Constant plus      => "(Prelude.+)".
Extract Inlined Constant predn     => "Prelude.pred".
Extract Inlined Constant proj1_sig => "".
Extract Inlined Constant projT1    => "Prelude.fst".
Extract Inlined Constant size      => "Data.List.length".
Extract Inlined Constant snd       => "Prelude.snd".
Extract Inlined Constant subn      => "(Prelude.-)".

Extraction Implicit eq_rect [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec [ x y ].
Extraction Implicit eq_rec_r [ x y ].

Extract Inlined Constant eq_rect => "".
Extract Inlined Constant eq_rect_r => "".
Extract Inlined Constant eq_rec => "".
Extract Inlined Constant eq_rec_r => "".

Extraction Implicit funcomp [ u ].

Extract Inlined Constant funcomp => "(Prelude..)".

Extract Inductive simpl_fun => "(->)" [""].

Extract Inlined Constant fun_of_simpl => "(Prelude.$)".
Extract Inlined Constant SimplRel => "".

Extract Inlined Constant ord_max => "".

Extraction Implicit nat_of_ord [ n ].
Extraction Implicit widen_ord [ n m ].

Extract Inlined Constant nat_of_ord => "".
Extract Inlined Constant widen_ord => "".

Extract Inlined Constant ssr_have => "(Prelude.flip (Prelude.$))".
