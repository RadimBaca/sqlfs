

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
Notation d_mid := (Attr_Z "d.mid").
Notation d_pid := (Attr_Z "d.pid").
Notation p_pid := (Attr_Z "p.pid").
Notation m_mid := (Attr_Z "m.mid").

Print attribute.


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




(* Support definitions  *)
Definition AttrExpr (a : (attribute TNull)):= A_Expr _ (F_Dot _ a).
Definition ConstExpr (v : Z):= A_Expr TNull (F_Constant TNull (Value_Z (Some v))).
Definition FromWithoutAlias (name : string):= From_Item (Sql_Table TNull (Rel name)) (Att_Ren_Star TNull).
Definition basesort_map := _basesort TNull db_movie.
Definition database_map := _instance TNull db_movie.
(* Notation basessort := _basesort TNull db_movie. -- Proc toto nemohu udelat? *)
Definition bool_type := (Bool.b (Tuple.B TNull)).
Definition sql_true_formula := Sql_True TNull (sql_query TNull relname).



(* Q7 - SELECT * FROM Movie, Director *)
Definition sql7 := Sql_Select 
  (Select_Star TNull)
  ((FromWithoutAlias "movie")::(FromWithoutAlias "director"):: nil)
  sql_true_formula
  (Group_Fine TNull)
  sql_true_formula.
  
Compute eval_sql_query basesort_map database_map _ _ nil sql7.

Definition q7 := sql_query_to_alg basesort_map sql7.

(* Definition q7 := Q_Sigma (Sql_True TNull (query TNull relname))
(Q_Sigma (Sql_True TNull (query TNull relname))
   (Q_NaturalJoin (Q_Table TNull (Rel "movie"))
      (Q_NaturalJoin (Q_Table TNull (Rel "director"))
         (Q_Empty_Tuple TNull relname)))). *)

         
Compute eval_query basesort_map database_map _ _ _ q7.
