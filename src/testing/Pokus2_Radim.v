

Set Implicit Arguments.

Require Import Relations SetoidList List String Ascii Bool ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula Sql.

Require Import Values TuplesImpl GenericInstance SqlSyntax SqlAlgebra.

Import Tuple.
Import NullValues. 

Definition db0 := init_db_ TNull.

Notation year := (Attr_Z "year").
Notation firstname := (Attr_string "firstname").
Notation lastname := (Attr_string "lastname").
Notation title := (Attr_string "title").
Notation name := (Attr_string "name").
Notation r_mid := (Attr_Z "r.mid").
Notation runtime := (Attr_Z "runtime").
Notation rank := (Attr_Z "rank").
Notation r_pid := (Attr_Z "r.pid").
Notation d_mid := (Attr_Z "mid").
Notation d_pid := (Attr_Z "d.pid").
Notation p_pid := (Attr_Z "p.pid").
Notation m_mid := (Attr_Z "mid").


Definition persons := Fset.mk_set (A TNull) (p_pid :: firstname :: lastname :: nil).

(* Je mozne si nejak vypsat obsah persons Fset?  *)

(* role: mid, pid, name *)
Definition mk_role mid pid n :=
  mk_tuple 
    TNull
    (Fset.mk_set _ (r_mid :: r_pid :: name :: nil))
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
    (Fset.mk_set _ (d_mid :: d_pid :: nil))
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
    (Fset.mk_set _ (p_pid :: firstname :: lastname :: nil))
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
    (Fset.mk_set _ (m_mid :: title :: year :: runtime :: rank :: nil))
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


(* The following code test the Fset implementation on numbers. *)
Search (N -> N -> comparison).
Definition Oset_nat : Oset.Rcd N.
Proof.
split with N.compare. 
- intros a1 a2; unfold N.compare.
Admitted.
Definition Fset_nat := Fset.build Oset_nat.
Definition nat_set1 := Fset.mk_set Fset_nat (1::2::nil).
Check nat_set1.
Compute Fset.elements Fset_nat nat_set1.





Definition create_schema :=
create_table
  (create_table
     (create_table
        (create_table  db0 (Rel "role") (r_mid :: r_pid :: name :: nil))
        (Rel "director") (d_mid :: d_pid :: nil))
     (Rel "people") (p_pid :: firstname :: lastname :: nil))
  (Rel "movie") (m_mid :: title :: year :: runtime :: rank :: nil).

Definition create_db roles directors people movies :=
  insert_tuples_into 
    (insert_tuples_into
       (insert_tuples_into
          (insert_tuples_into create_schema movies (Rel "movie"))
          people (Rel "people"))
       directors (Rel "director"))
    roles (Rel "role").

Definition db_movie := create_db roles directors people movies.




Definition v1 : value := Value_bool (Some true).
(* Definition v2 : value := Value_string (Some "retezec"). *)
Compute show_state_ TNull db_movie.

(* Q1 - NaturalJoin(director, movie)*)
Definition Q1 := Q_NaturalJoin (Q_Table TNull (Rel "director")) (Q_Table TNull (Rel "movie")).

Definition basesort_map := _basesort TNull db_movie.
Definition database_map := _instance TNull db_movie.
(* Notation basessort := _basesort TNull db_movie. -- Proc toto nemohu udelat? *)
Definition bool_type := (Bool.b (Tuple.B TNull)).
Definition sql_true_formula := Sql_True TNull (sql_query TNull relname).


 Compute Fset.elements (A TNull) (sort basesort_map Q1).  (* Seznam promennych Q1 *)
Compute Fset.elements (A TNull) (free_variables_q basesort_map Q1).  (* Seznam volnych promennych Q1 *)

(* Check eval_query basesort_map database_map (Bool.b (Tuple.B TNull)) (env TNull) Q1. *)

Compute eval_query basesort_map database_map _ _ _ Q1.

Compute alg_query_to_sql basesort_map  _ _ _ Q1.


(* Support definitions  *)
Definition AttrExpr (a : (attribute TNull)):= A_Expr _ (F_Dot _ a).
Definition ConstExpr (v : Z):= A_Expr TNull (F_Constant TNull (Value_Z (Some v))).
Definition FromWithoutAlias (name : string):= From_Item (Sql_Table TNull (Rel name)) (Att_Ren_Star TNull).


(* Q2  - Sigma_{year = 2001}(movie) *)
Definition Pr2 := (Predicate "=") : predicate TNull.
Definition Terms2 := AttrExpr year::ConstExpr 2001%Z::nil.  
Definition Formula1 := Sql_Pred (query TNull relname) Pr2 Terms2.
Definition Q2 := Q_Sigma Formula1
                    (Q_Table TNull (Rel "movie")).

Compute eval_query basesort_map database_map _ _ _ Q2.
(* Compute well_formed_q  basesort_map _ Q2. *)

(* Bool 3, tree of query *)

Compute Bool.andb (B TNull) true3 true3.
Compute Bool.andb (B TNull) true3 unknown3.
Check tree_of_query.
Compute tree_of_query Q2.
Compute alg_query_to_sql basesort_map  _ _ _ Q2.

(* Freshes *)
Definition first_attr (la : list (attribute TNull)) : attribute TNull := 
    match la with
    | nil => Attr_string ""
    | a :: t => a
    end.

Definition attributes := title :: lastname :: m_mid :: year :: nil.
(* Compute freshes TNull first_attr 4 attributes.  *)

(* Q3 - SELECT * FROM Movie WHERE year = 2001 *)
Definition p3 := (Values.Predicate "="): predicate TNull.
Definition sql3 := Sql_Select (Select_Star TNull)
    ((FromWithoutAlias "movie"):: nil)
    (Sql_Pred (sql_query TNull relname) p3
      (A_Expr TNull (F_Dot TNull year)
        :: A_Expr TNull (F_Constant TNull (Value_Z (Some 2001%Z)))
          :: nil))
    (Group_Fine TNull)
    sql_true_formula.


Compute eval_sql_query basesort_map database_map _ _ _ sql3.


(* Q4 - SELECT * FROM (SELECT title, title FROM Movie) *)
Definition select_as_attr (attr : attribute TNull):= (Select_As TNull (AttrExpr attr) attr).
Definition select_list := (Select_List TNull (_Select_List TNull ((select_as_attr title)::(select_as_attr title)::nil))).
Definition sub_select4 := Sql_Select select_list
  ((FromWithoutAlias "movie"):: nil)
  sql_true_formula
  (Group_Fine TNull)
  sql_true_formula.
Definition sql4 := Sql_Select (Select_Star TNull)
    (From_Item sub_select4 (Att_Ren_Star TNull):: nil)
    sql_true_formula
    (Group_Fine TNull)
    sql_true_formula.
    
Compute eval_sql_query basesort_map database_map _ _ _ sub_select4.
Compute eval_sql_query basesort_map database_map _ _ _ sql4.
Compute Fset.elements _ (sql_sort basesort_map sub_select4).


(* TODO: 
- napsat sql_formula se zavislym poddotazem a volnyma promennyma
- testing wellformed
*)


(* Q5 - SELECT * FROM Movie WHERE year = "2001" *)
(* 
SQL query with incorrect data types in predicate
*)
Definition p5 := (Values.Predicate "="): predicate TNull.
Definition sql5 := Sql_Select (Select_Star TNull)
    ((FromWithoutAlias "movie"):: nil)
    (Sql_Pred (sql_query TNull relname) p5
      (A_Expr TNull (F_Dot TNull year)
        :: A_Expr TNull (F_Constant TNull (Value_string (Some "2001"%string)))
          :: nil))
    (Group_Fine TNull)
    sql_true_formula.

Compute eval_sql_query basesort_map database_map _ _ nil sql5.

(* Q6 - SELECT * FROM Movie, Director WHERE m_mid = d_mid *)
Definition p6 := (Values.Predicate "="): predicate TNull.
Definition f6 := Sql_Pred (sql_query TNull relname) p6
  (AttrExpr d_mid :: AttrExpr m_mid :: nil).
Definition sql6 := Sql_Select 
  (Select_Star TNull)
  ((FromWithoutAlias "movie")::(FromWithoutAlias "director"):: nil)
  f6
  (Group_Fine TNull)
  sql_true_formula.
  
Compute eval_sql_query basesort_map database_map _ _ nil sql6.

Definition q6 := sql_query_to_alg basesort_map sql6.
Compute q6.



(* Q7 - SELECT * FROM Movie, Director *)
Definition sql7 := Sql_Select 
  (Select_Star TNull)
  ((FromWithoutAlias "movie")::(FromWithoutAlias "director"):: nil)
  sql_true_formula
  (Group_Fine TNull)
  sql_true_formula.
  
Compute eval_sql_query basesort_map database_map _ _ nil sql7.

Compute sql_query_to_alg basesort_map sql7.

Definition q7 := Q_Sigma (Sql_True TNull (query TNull relname))
(Q_Sigma (Sql_True TNull (query TNull relname))
   (Q_NaturalJoin (Q_Table TNull (Rel "movie"))
      (Q_NaturalJoin (Q_Table TNull (Rel "director"))
         (Q_Empty_Tuple TNull relname)))).

         
Compute eval_query basesort_map database_map _ _ _ q7.