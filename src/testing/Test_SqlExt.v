

Set Implicit Arguments.

Require Import Relations SetoidList List String Ascii Bool ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula Sql.

Require Import Values TuplesImpl GenericInstanceExt SqlSyntaxExt SqlAlgebra SqlExt SqlAlgebraExt.

Import Tuple.
Import NullValues. 

Definition db0 := init_db_ext_ TNull.

Notation year := (Attr_Z "year").
Notation firstname := (Attr_string "firstname").
Notation lastname := (Attr_string "lastname").
Notation title := (Attr_string "title").
Notation name := (Attr_string "name").
Notation r_mid := (Attr_Z "r.mid").
Notation runtime := (Attr_Z "runtime").
Notation rank := (Attr_Z "rank").
Notation r_pid := (Attr_Z "r.pid").
Notation d_mid := (Attr_Z "d.mid").
Notation d_pid := (Attr_Z "d.pid").
Notation p_pid := (Attr_Z "p.pid").
Notation m_mid := (Attr_Z "m.mid").


Definition role_attr_list := r_mid :: r_pid :: name :: nil.
Definition director_attr_list := d_mid :: d_pid :: nil.
Definition persons_attr_list := p_pid :: firstname :: lastname :: nil.
Definition movie_attr_list := m_mid :: title :: year :: runtime :: rank :: nil.

Definition role_ucc_list := r_mid :: r_pid :: nil.
Definition director_ucc_list := d_mid :: d_pid :: nil.
Definition persons_ucc_list := p_pid :: nil.
Definition movie_ucc_list := m_mid :: nil.

(* role: mid, pid, name *)
Definition mk_role mid pid n :=
  mk_tuple 
    TNull
    (Fset.mk_set _ role_attr_list)
    (fun a => match a with
              | r_mid => Value_Z (Some mid)
              | r_pid => Value_Z (Some pid)
              | name => Value_string (Some n)
              | Attr_string _ => Value_string None
              | Attr_Z _ => Value_Z None
              | Attr_bool _ => Value_bool None
              end).

Definition roles :=
  mk_role 2120 640 "Man with Knife"
    :: mk_role 2120 715 "J.J. Gittes"
    :: mk_role 2279 2330 "Cliff Stern"
    :: mk_role 2279 874 "Judah Rosenthal"
    :: mk_role 2406 4970 "Shrek"
    :: mk_role 2406 4972 "Princess Fiona"
    :: mk_role 2139 1805 "'Maxim' de Winter"
    :: mk_role 2139 1806 "Mrs. de Winter"
    :: nil.

(* director: mid, pid *)
Definition mk_director mid pid :=
  mk_tuple 
    TNull
    (Fset.mk_set _ director_attr_list)
    (fun a => match a with
              | d_mid => Value_Z (Some mid)
              | d_pid => Value_Z (Some pid)
              | Attr_string _ => Value_string None
              | Attr_Z _ => Value_Z None
              | Attr_bool _ => Value_bool None
              end).

Definition directors :=
  mk_director 2120 640
    :: mk_director 2279 2330
    :: mk_director 2406 4969
    :: nil.


(* people: pid, firstname, lastname *)
Definition mk_people pid f l :=
  mk_tuple
    TNull
    (Fset.mk_set _ persons_attr_list)
    (fun a => match a with
              | p_pid => Value_Z (Some pid)
              | firstname => Value_string (Some f)
              | lastname => Value_string (Some l)
              | Attr_string _ => Value_string None
              | Attr_Z _ => Value_Z None
              | Attr_bool _ => Value_bool None
              end).

Definition people :=
  mk_people 640 "Roman" "Polanski"
    :: mk_people 715 "Jack" "Nicholson"
    :: mk_people 2330 "Woody" "Allen"
    :: mk_people 874 "Martin" "Landau"
    :: mk_people 4970 "Mike" "Myers"
    :: mk_people 4972 "Cameron" "Diaz"
    :: mk_people 1805 "Laurence" "Olivier"
    :: mk_people 1806 "Joan" "Fontaine"
    :: mk_people 4969 "Vicky" "Jenson"
    :: mk_people 464 "Alfred" "Hitchcock"
    :: nil.



    (* movie: mid, title, year, runtime, rank *)
Definition mk_movie mid t y rt rk :=
  mk_tuple
    TNull
    (Fset.mk_set _ movie_attr_list)
    (fun a => match a with
              | m_mid => Value_Z (Some mid)
              | title => Value_string (Some t)
              | year => Value_Z (Some y)
              | runtime => Value_Z (Some rt)
              | rank => Value_Z (Some rk)
              | Attr_string _ => Value_string None
              | Attr_Z _ => Value_Z None
              | Attr_bool _ => Value_bool None
              end).

Definition movies :=
  mk_movie 2120 "Chinatown" 1974 130 121
    :: mk_movie 2279 "Crimes and Misdemeanors" 1989 104 280
    :: mk_movie 2406 "Shrek" 2001 90 407
    :: mk_movie 2139 "Rebecca" 1940 130 140
    :: nil.







Compute mk_director 2279 23300.
Definition r1 := mk_role 2120 640 "Man with Knife".
Compute dot TNull r1 name.
Compute dot TNull r1 r_mid.
Check labels TNull r1.
(* Converting Fset.set on list X using Fset.elements function. *)
Compute Fset.elements (Tuple.A TNull) (labels TNull r1).
(* Print list of (attribute, value) pairs *)
Compute show_tuple TNull r1.
(* TNull represents an implementation of Tuple.Rcd interface.
We pass the TNull implementation to the call of each function wotking with the interface. *)





Definition create_schema :=
create_table
  (create_table
     (create_table
        (create_table  db0 (Rel "role") role_attr_list role_ucc_list)
        (Rel "director") director_attr_list director_ucc_list)
     (Rel "people") persons_attr_list persons_ucc_list)
  (Rel "movie") movie_attr_list movie_ucc_list.

Definition create_db roles directors people movies :=
  insert_tuples_into 
    (insert_tuples_into
       (insert_tuples_into
          (insert_tuples_into create_schema movies (Rel "movie"))
          people (Rel "people"))
       directors (Rel "director"))
    roles (Rel "role").

Definition db_movie := create_db roles directors people movies.




(* Freshes *)
Definition first_attr (la : list (attribute TNull)) : attribute TNull := 
    match la with
    | nil => Attr_string ""
    | a :: t => a
    end.

Definition attributes := title :: lastname :: m_mid :: year :: nil.
(* Compute freshes TNull first_attr 4 attributes.  *)


(* Support definitions  *)
Definition AttrExpr (a : (attribute TNull)):= A_Expr _ (F_Dot _ a).
Definition ConstExpr (v : Z):= A_Expr TNull (F_Constant TNull (Value_Z (Some v))).
Definition FromWithoutAlias (tablename : string):= From_Item_Ext (Sql_Table_Ext TNull (Rel tablename)) (Att_Ren_Star TNull).
Definition JoinWithoutAlias (tablename : string) f := Join_Item (Inner_Join) (Sql_Table_Ext TNull (Rel tablename)) (Att_Ren_Star TNull) f.

Definition basesort_map := _basesort TNull db_movie.
Definition database_map := _instance TNull db_movie.
Definition pk_map := _pk TNull db_movie.
(* Notation basessort := _basesort TNull db_movie. -- Proc toto nemohu udelat? *)
Definition bool_type := (Bool.b (Tuple.B TNull)).
Definition sql_true_formula := Sql_True TNull (sql_query_ext TNull relname).



(* Q3 - SELECT * FROM Movie WHERE year = 2001 *)
Definition p3 := (Values.Predicate "="): predicate TNull.
Definition sql3 : sql_query_ext TNull relname := Sql_Select_Ext (Select_Star TNull)
    (FromWithoutAlias "movie")
    nil
    (Sql_Pred (sql_query_ext TNull relname) p3
      (A_Expr TNull (F_Dot TNull year)
        :: A_Expr TNull (F_Constant TNull (Value_Z (Some 2001%Z)))
          :: nil))
    (Group_Fine TNull)
    sql_true_formula.


Compute eval_sql_query_ext basesort_map database_map _ _ _ sql3.



(* Q6 - SELECT * FROM Movie JOIN Director ON m_mid = d_mid *)
Definition p6 := (Values.Predicate "="): predicate TNull.
Definition f6 := Sql_Pred (sql_query_ext TNull relname) p6
  (AttrExpr d_mid :: AttrExpr m_mid :: nil).
Definition sql6 := Sql_Select_Ext 
  (Select_Star TNull)
  (FromWithoutAlias "movie")
  ((JoinWithoutAlias "director" f6):: nil)
  sql_true_formula
  (Group_Fine TNull)
  sql_true_formula.
  
Compute eval_sql_query_ext basesort_map database_map _ _ nil sql6.

Definition alg_sql6 := sql_query_ext_to_alg basesort_map sql6.
Compute eval_query basesort_map database_map _ _ _ alg_sql6.

Definition norm_sql6 := sql_query_ext_to_sql_query sql6.
Compute sql6.
Compute norm_sql6.
Compute eval_sql_query basesort_map database_map _ _ nil norm_sql6.


(* testing N_Q_NaturalJoin *)

Definition p7 := (Values.Predicate "="): predicate TNull.
Definition f7 := Sql_Pred (query TNull relname) p7 
  (AttrExpr d_mid :: AttrExpr m_mid :: nil).

Definition j7 := sql_query_ext_to_alg basesort_map (Sql_Table_Ext TNull (Rel "director")).
Definition fr7 := sql_query_ext_to_alg basesort_map (Sql_Table_Ext TNull (Rel "movie")).
Compute N_Q_NaturalJoin fr7 ((f7, j7) :: nil).


(* Jak udelat self-join? *)
