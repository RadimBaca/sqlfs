(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**                       LMF, CNRS & Université Paris-Saclay                       *)
(**                       VSB - Technical University of Ostrava                     *)
(**                                                                                 *)
(**                        Copyright 2016-2024 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                  Radim Baca                                                     *)
(**                  Zdenek Sawa                                                    *)
(**                  Martin Kot                                                     *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.
Require Import Bool List Arith NArith Psatz.

Require Import BasicTacs BasicFacts ListFacts ListPermut ListSort OrderedSet
        FiniteSet FiniteBag FiniteCollection Join FlatData Tree Term Bool3 Formula 
        Partition Sql SqlExt SqlAlgebra.

Section Sec.

Hypothesis T : Tuple.Rcd.

Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.

Notation predicate := (Tuple.predicate T).
Notation symb := (Tuple.symbol T).
Notation aggregate := (Tuple.aggregate T).
Notation OPredicate := (Tuple.OPred T).
Notation OSymb := (Tuple.OSymb T).
Notation OAggregate := (Tuple.OAgg T).

Import Tuple.

Notation value := (value T).
Notation attribute := (attribute T).
Notation tuple := (tuple T).
Arguments funterm {T}.
Arguments aggterm {T}.
Arguments Select_Star {T}.
Arguments Select_As {T}.
Arguments Select_List {T}.
Arguments _Select_List {T}.
Arguments Group_Fine {T}.
Arguments Group_By {T}.
Arguments F_Dot {T}.
Arguments A_Expr {T}.
Arguments Sql_True {T}.
Arguments Sql_Pred {T}.
Arguments Sql_Quant {T}.
Arguments Sql_In {T}.
Arguments Sql_Exists {T}.



Notation sql_formula := (sql_formula T query). 

Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Notation interp_funterm := (interp_funterm T).
Notation interp_aggterm := (interp_aggterm T).
Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> bagT.

Definition Q_ThetaJoin f (q1 : query T relname) (q2 : query T relname) := Q_Sigma f (Q_NaturalJoin q1 q2).


(* sql_query_ext_to_alg *)

Fixpoint N_Q_NaturalJoin sq l :=
  match l with
    | nil => sq
    | (f, q1) :: l' => Q_ThetaJoin f q1 (N_Q_NaturalJoin sq l')
  end.


Fixpoint sql_query_ext_to_alg (sq : sql_query_ext T relname) :=
  match sq with
    | Sql_Table_Ext _ r => Q_Table T r
    | Sql_Set_Ext o sq1 sq2 => Q_Set o (sql_query_ext_to_alg sq1) (sql_query_ext_to_alg sq2)
    | Sql_Select_Ext s lsq jq f1 g f2 =>
      let sql_formula_to_alg :=
          (fix sql_formula_to_alg f  :=
             match f with
             | Sql_Conj a f1 f2 => Sql_Conj a (sql_formula_to_alg f1) (sql_formula_to_alg f2)
             | Sql_Not f => Sql_Not (sql_formula_to_alg f)
             | Sql_True _ => Sql_True _
             | Sql_Pred _ p l => Sql_Pred _ p l
             | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (sql_query_ext_to_alg sq)
             | Sql_In _ s sq => Sql_In _ s (sql_query_ext_to_alg sq)
             | Sql_Exists _ sq => Sql_Exists _ (sql_query_ext_to_alg sq)
             end) in 
      match s with
      | Select_Star =>
        let s := _Select_List (id_renaming _ (sql_ext_sort basesort sq)) in
        let q1 := sql_item_to_alg lsq in 
        let q2 := N_Q_NaturalJoin q1 (map sql_join_item_to_alg jq) in
        let q3 := Q_Sigma (sql_formula_to_alg f1) q2 in 
        match g with
        | Group_Fine => Q_Sigma (sql_formula_to_alg f2) q3 
        | Group_By g => Q_Gamma s g (sql_formula_to_alg f2) q3 
        end
      | Select_List s =>
        (* let q1 := Q_NaturalJoin (Q_Empty_Tuple T relname) (sql_item_to_alg lsq) in  *)
        let q1 := sql_item_to_alg lsq in 
        let q2 := N_Q_NaturalJoin q1 (map sql_join_item_to_alg jq) in
        let q3 := Q_Sigma (sql_formula_to_alg f1) q2 in 
        match g with
        | Group_Fine => Q_Pi s (Q_Sigma (sql_formula_to_alg f2) q3) 
        | Group_By g => Q_Gamma s g (sql_formula_to_alg f2) q3 
        end
      end
  end

with sql_item_to_alg i :=
  match i with
    | From_Item_Ext sq (Att_Ren_Star _) => sql_query_ext_to_alg sq
    | From_Item_Ext sq (Att_Ren_List s) =>
      Q_Pi 
        (_Select_List
           (map (fun x => match x with Att_As _ a a' => Select_As (A_Expr (F_Dot a)) a' end) s))
        (sql_query_ext_to_alg sq)
  end
with sql_join_item_to_alg i :=
     let sql_formula_to_alg := (* TODO - avoid duplicit defitnition of sql_formula_to_alg *)
        (fix sql_formula_to_alg f  :=
        match f with
        | Sql_Conj a f1 f2 => Sql_Conj a (sql_formula_to_alg f1) (sql_formula_to_alg f2)
        | Sql_Not f => Sql_Not (sql_formula_to_alg f)
        | Sql_True _ => Sql_True _
        | Sql_Pred _ p l => Sql_Pred _ p l
        | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (sql_query_ext_to_alg sq)
        | Sql_In _ s sq => Sql_In _ s (sql_query_ext_to_alg sq)
        | Sql_Exists _ sq => Sql_Exists _ (sql_query_ext_to_alg sq)
        end) in 
    match i with
        | Join_Item _ sq (Att_Ren_Star _) f => (sql_formula_to_alg f, sql_query_ext_to_alg sq)
        | Join_Item _ sq (Att_Ren_List s) f => (sql_formula_to_alg f,
        Q_Pi 
            (_Select_List
                (map (fun x => match x with Att_As _ a a' => Select_As (A_Expr (F_Dot a)) a' end) s))
            (sql_query_ext_to_alg sq))
    end.

End Sec.