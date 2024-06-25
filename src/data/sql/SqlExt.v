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

(** printing inS? $\in_?$ #∈<SUB>?</SUB># *)
(** printing inS $\in$ #∈# *)(** printing subS? $\subseteq_?$ #⊆<SUB>?</SUB># *)
(** printing subS $\subseteq$ #⊆# *)
(** printing unionS $\cup$ #⋃# *)
(** printing interS $\cap$ #⋂# *)
(** printing inI $\in_I$ #∈<SUB><I>I</I></SUB># *)
(** printing theta $\theta$ #θ# *)
(** printing nu1 $\nu_1$ #ν<SUB><I>1</I></SUB># *)
(** printing nu $\nu$ #ν# *)
(** printing mu $\mu$ #μ# *)
(** printing sigma $\sigma$ #σ# *)
(** printing -> #⟶# *)
(** printing <-> #⟷# *)
(** printing => #⟹# *)
(** printing (emptysetS) $\emptyset$ #Ø# *)
(** printing emptysetS $\emptyset$ #Ø# *)
(** printing {{ $\{$ #{# *)
(** printing }} $\}$ #}# *)

Require Import Relations SetoidList List String Ascii Bool ZArith NArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet 
        FiniteSet FiniteBag FiniteCollection Join FlatData Tree Bool3 Formula 
        Partition Sql Projection.


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
(* Arguments att_renaming_item {T}. *)
Notation att_renaming_item := (att_renaming_item T).

Inductive join_type : Type :=
  | Cross_Join
  | Inner_Join
  (* | Outer_Left_Join *)
  (* | Outer_Right_Join *)
  (* | D_Join *).

Inductive sql_query_ext : Type := 
  | Sql_Table : relname -> sql_query_ext 
  | Sql_Set : set_op -> sql_query_ext -> sql_query_ext -> sql_query_ext 
  | Sql_Select : 
      (** select *) select_item T ->
      (** from *) sql_from_item_ext ->
      (** join *) list sql_join_item_ext -> 
      (** where *) sql_formula T sql_query_ext ->
      (** group by *) group_by T ->
      (** having *) sql_formula T sql_query_ext -> sql_query_ext
      
with sql_from_item_ext : Type := 
| From_Item : sql_query_ext -> att_renaming_item -> sql_from_item_ext
with sql_join_item_ext : Type :=
| Join_Item : join_type -> sql_query_ext -> att_renaming_item -> sql_formula T sql_query_ext -> sql_join_item_ext.








(** * SQL_COQ semantics *)
Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> bagT.

Definition select_as_as_pair (x : select T) := match x with Select_As _ e a => (e, a) end.
Definition att_as_as_pair (x : att_renaming T) := match x with Att_As _ e a => (e, a) end.
(** TODO : this is defined in Sql.v as well, why I cannot use it? *)

Fixpoint sql_ext_sort (sq : sql_query_ext) : setA :=
  match sq with
    | Sql_Table tbl => basesort tbl
    | Sql_Set o sq1 _ => sql_ext_sort sq1 
    | Sql_Select s f j _ _ _ => 
      match s with
        | Select_Star  => Fset.union (A T) (sql_from_item_sort f) (Fset.Union (A T) (List.map sql_join_item_sort j))
        | Select_List (_Select_List la) => 
           Fset.mk_set (A T) (List.map (@snd _ _) (List.map select_as_as_pair la))
      end
  end
with sql_from_item_sort x :=
  match x with
    | From_Item sq (Att_Ren_Star _) => sql_ext_sort sq
    | From_Item _ (Att_Ren_List la) =>
           Fset.mk_set (A T) (List.map (@snd _ _) (List.map att_as_as_pair la))
  end
with sql_join_item_sort x :=
  match x with
    | Join_Item _ sq (Att_Ren_Star _) _ => sql_ext_sort sq
    | Join_Item _ _ (Att_Ren_List la) _ =>
           Fset.mk_set (A T) (List.map (@snd _ _) (List.map att_as_as_pair la))
  end.


(** * evaluation of SQL queries *)
Hypothesis unknown : Bool.b (B T).
Hypothesis contains_nulls : tuple -> bool.
Hypothesis contains_nulls_eq : forall t1 t2, t1 =t= t2 -> contains_nulls t1 = contains_nulls t2.

Notation eval_sql_formula := (eval_sql_formula (T := T) (dom := sql_query_ext) unknown contains_nulls).
(* Evaluation in an environment :-( *)

Notation make_groups := 
  (fun env b => @make_groups T env (Febag.elements (Fecol.CBag (CTuple T)) b)).

  
Fixpoint eval_sql_query_ext env (sq : sql_query_ext) {struct sq} : bagT :=
  match sq with
  | Sql_Table tbl => instance tbl
  | Sql_Set o sq1 sq2 =>
    if sql_ext_sort sq1 =S?= sql_ext_sort sq2 
    then Febag.interp_set_op _ o (eval_sql_query_ext env sq1) (eval_sql_query_ext env sq2)
    else Febag.empty _
  | Sql_Select s lsq jq f1 gby f2  => 
    let elsq := 
        eval_sql_ext_from_item env lsq in
    let cc :=
        (** selection of the from part by the where formula f1 (with old names) *)
        Febag.mk_bag (Fecol.CBag (CTuple T)) 
            (List.filter 
            (fun t => 
                Bool.is_true 
                _ 
                (eval_sql_formula eval_sql_query_ext (env_t T env t) f1)) 
            (List.fold_right (eval_sql_ext_join_item env) (Febag.elements (Fecol.CBag (CTuple T)) elsq) jq)) in
    (** computation of the groups grouped according to gby *)
       let lg1 := make_groups env cc gby in
       (** discarding groups according the having clause f2 *)
       let lg2 := 
           List.filter 
             (fun g  => Bool.is_true _ (eval_sql_formula eval_sql_query_ext (env_g T env gby g) f2))
             lg1 in
       (** applying the outermost projection and renaming, the select part s *)
       Febag.mk_bag BTupleT
                    (List.map (fun g => projection T (env_g T env gby g) s) lg2)
  end

(** * evaluation of the from part *)
with eval_sql_ext_from_item env x := 
       match x with
         | From_Item sqj sj =>
           Febag.map BTupleT BTupleT 
             (fun t => 
                projection T (env_t T env t) (att_renaming_item_to_from_item sj)) 
             (eval_sql_query_ext env sqj)
       end
with eval_sql_ext_join_item env ji br :=
        match ji with
        | Join_Item jt sqj sj f => (** TODO: join type *)
            List.filter 
            (fun t => 
                Bool.is_true 
                _ 
                (eval_sql_formula eval_sql_query_ext (env_t T env t) f)) 
                (brute_left_join_list _ (join_tuple T)
                    (Febag.elements (Fecol.CBag (CTuple T)) 
                        (Febag.map BTupleT BTupleT 
                        (fun t => 
                            projection T (env_t T env t) (att_renaming_item_to_from_item sj)) 
                        (eval_sql_query_ext env sqj)))
                    br)
        end.


       End Sec.