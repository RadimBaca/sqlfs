
From Coq Require Import String.
From Coq Require Decimal DecimalNat DecimalString List.

Require Import Mem OrderedSet.
Require Import FTuples GenericInstance.

Import List.ListNotations.

Open Scope string_scope.
Open Scope list_scope.



Definition nat_to_str (n : nat) : string :=
    let u := Decimal.rev (DecimalNat.Unsigned.to_lu n) in
    DecimalString.NilZero.string_of_uint u.


Definition create_name (name : string) (n : nat) :=
    String.append name (nat_to_str n).


Definition name_in_list (s : string) (l : list string) : bool :=
    Mem.mem_bool eqb s l.


Section Gen_name.

  Variable name : string.

  Variable name_list : list string.

  Fixpoint gen_name_aux (n : nat) (count : nat) : string
     := let new_name := create_name name n in
        match count with
        | 0 => new_name
        | S count' => 
            if name_in_list new_name name_list then
                 gen_name_aux (S n) count'
            else new_name
        end.

  Definition gen_name : string
        := gen_name_aux 0 (S (Datatypes.length name_list)).

End Gen_name.


Example gen_name_ex1: 
   gen_name "x" [ "x3"; "y0"; "x1"; "x4"; "x0"; "x2" ] = "x5".
Proof. reflexivity. Qed.



Definition name_of_attribute (a : attribute) : string
    := match a with
       | Attr_string name
       | Attr_Z name
       | Attr_bool name => name
       end.

Definition names_of_attributes (l : list attribute) : list string
     := List.map name_of_attribute l.


Definition fresh_attr (a : attribute) (l : list attribute) : attribute
   := let name := gen_name (name_of_attribute a) (names_of_attributes l) in
      match a with
      | Attr_string _ => Attr_string name
      | Attr_Z _ => Attr_Z name
      | Attr_bool _ => Attr_bool name
      end.


Lemma fresh_attr_is_fresh : forall a s,
     Oset.mem_bool OAN (fresh_attr a s) s = false.
Proof.
  intros a s.
Admitted.









