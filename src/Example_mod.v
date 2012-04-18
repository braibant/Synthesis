Require Import Common. 
Require Import TRS. 

Definition Num : type1 := T01 (Tint 32). 
Definition Val : type1 :=
  Tunion "Val" ("MOD" of (Ttuple [Num; Num]) 
               :: "VAL" of (Ttuple [Num]) 
               :: type1_id_list_nil ). 

Definition mod_iterate_rule : rule [Treg Val]. 
set (env := [Treg Num; Treg Num]). 
set (a := var_0 : var env (Treg Num)). 
set (b := var_S var_0 : var env (Treg Num)). 
apply (mk_rule' env). 

Definition pattern2_vector_singleton E t x :=
  pattern2_vector_cons E _ t _ x pattern2_vector_nil. 
apply (pattern2_vector_singleton env). 
apply Plift. 
eapply Punion.  apply  (pattern1_disjunct_hd). 
apply ([| Pvar1 Num, Pvar1 Num |])%pattern. 
    
apply (! b <= ! a)%expr. 


Definition expr2_vector_singleton E t (x : @expr2 E t) : expr2_vector E [t] :=
  dlist_cons t [] x (@dlist_nil type2 expr2). 

apply expr2_vector_singleton. 
eapply Eset. eapply Eunion. eapply expr1_disjunct_hd.  apply ([| !a - !b, !b|])%expr. 
Defined. 

Definition mod_done_rule : rule [Treg Val]. 
set (env := [Treg Num; Treg Num]). 
set (a := var_0 : var env (Treg Num)). 
set (b := var_S var_0 : var env (Treg Num)). 
apply (mk_rule' env). 
    
apply (pattern2_vector_singleton env). 
apply Plift. eapply Punion. apply pattern1_disjunct_hd. 
apply ([| Pvar1 Num, Pvar1 Num |])%pattern. 

apply (!a < !b)%expr. 

apply expr2_vector_singleton. 
apply Eset. 
apply Eunion. apply expr1_disjunct_tl. apply expr1_disjunct_hd.
apply ([| !a |])%expr. 
Defined. 
    
Definition TRS : TRS :=
  {| trs_type := [Treg Val]; 
     trs_rules := [mod_iterate_rule; mod_done_rule ]|}. 

Definition AA : Word.T 32 := Word.repr 32 31. 
Definition BB : Word.T 32 := Word.repr 32 3. 

Definition this_ENV : eval_env eval_type2 [Treg Num; Treg Num] := (AA, (BB, tt)). 

Eval compute in run_unfair 10 TRS ((inl this_ENV, tt)). 
