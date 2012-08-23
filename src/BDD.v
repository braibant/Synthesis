Require Import Common ZArith. 

Inductive expr := | F | T | N : positive -> expr. 

Notation var := nat. 

Definition node := (expr * var * expr)%type. 

Definition expr_eqb a b :=
  match a,b with 
    | T,T => true
    | F,F => true
    | N x, N y => (x =? y)%positive
    | _, _ => false
  end. 

Definition node_eqb (a b: node) :=
  match a with 
    | (xa,ya,za) => 
        match b with 
          | (xb,yb,zb) => (expr_eqb xa xb && (NPeano.Nat.eqb ya yb) && expr_eqb za zb)%bool
        end
  end. 

Fixpoint assoc {A B} (eq: A -> A ->  bool) x l : option B :=
  match l with 
    | nil => None
    | cons (u,v) q => if eq x u then Some v else assoc eq x q
  end. 

Module Inner. 
  Require Import FMapPositive. 
  
  Record BDD :=
    {
      tmap : list (positive * node)%type;
      hmap : list (node * positive)%type;
      next : positive
    }. 

  Definition empty :=
    {|
      tmap := nil;
      hmap := nil;
      next := 1
    |}.
         

  Definition mk_node bdd (l : expr) v (h : expr) :=
    if expr_eqb l  h then (l,bdd)
    else
      match assoc node_eqb (l,v,h) (hmap bdd) with 
          | Some x => (N x, bdd)
          | None => let n := (l,v,h) in 
                    let u := next bdd in 
                    let bdd := {|  tmap := (u,n) :: tmap bdd;
                                    hmap := (n,u) :: hmap bdd;
                                    next := (u + 1)%positive |} in
                      (N u, bdd)
       end. 

  Fixpoint andb bdd depth (a b : expr) : option (expr * BDD) :=
    match depth with 
      | 0 => None
      | S depth => 
          match a,b with 
            | F, _ => Some (F, bdd)
            | _, F => Some (F, bdd)
            | T, x => Some (x, bdd)
            | x, T => Some (x, bdd)
            | N na, N nb => 
                do na <- assoc Pos.eqb na (tmap bdd);
                do nb <- assoc Pos.eqb nb (tmap bdd);
                match na,nb with 
                  | (l1,v1,h1),(l2,v2,h2) =>
                      match NPeano.Nat.compare v1  v2 with 
                          | Eq =>
                              do  x ,bdd  <- andb bdd depth l1 l2;
                              do  y, bdd <- andb bdd depth h1 h2;
                              Some (mk_node bdd x v1 y)
                          | Lt =>
                              do x, bdd <- andb bdd depth l1 b;
                              do y, bdd <- andb bdd depth h1 b;
                              Some (mk_node bdd x v1 y)
                          | _ => 
                              do x, bdd <- andb bdd depth a l2;
                              do y, bdd <- andb bdd depth a h2;
                              Some (mk_node bdd x v2 y)
                end
          end
    end
       end.

  Fixpoint orb bdd depth (a b : expr) : option (expr * BDD) :=
    match depth with 
      | 0 => None
      | S depth => 
          match a,b with 
            | F, x => Some (x, bdd)
            | x, F => Some (x, bdd)
            | T, _ => Some (T, bdd)
            | _, T => Some (T, bdd)
            | N na, N nb => 
                do na <- assoc Pos.eqb na (tmap bdd);
                do nb <- assoc Pos.eqb nb (tmap bdd);
                match na,nb with 
                  | (l1,v1,h1),(l2,v2,h2) =>
                      match NPeano.Nat.compare v1  v2 with 
                          | Eq =>
                              do x, bdd <- orb bdd depth l1 l2;
                              do y, bdd <- orb bdd depth h1 h2;
                              Some (mk_node bdd x v1 y)
                          | Lt =>
                              do x, bdd <- orb bdd depth l1 b;
                              do y, bdd <- orb bdd depth h1 b;
                              Some (mk_node bdd x v1 y)
                          | _ => 
                              do x, bdd <- orb bdd depth a l2;
                              do y, bdd <- orb bdd depth a h2;
                              Some (mk_node bdd x v2 y)
                end
          end
    end
       end.



  Fixpoint negb bdd depth (a : expr) : option (expr * BDD) :=
    match depth with 
      | 0 => None
      | S depth => 
          match a with 
            | F => Some (T, bdd)
            | T => Some (F, bdd)
            | N na => 
                do na <- assoc Pos.eqb na (tmap bdd);
                match na with 
                  | (l,v,h) =>
                              do x, bdd <- negb bdd depth l;
                              do y, bdd <- negb bdd depth h;
                              Some (mk_node bdd x v y)
                end
          end
    end.

  Fixpoint xorb bdd depth (a b : expr) : option (expr * BDD) :=
    match depth with 
      | 0 => None
      | S depth => 
          match a,b with 
            | F, x => Some (x, bdd)
            | x, F => Some (x, bdd)
            | T, x => negb bdd depth x (* is this depth enough ?? *)
            | x, T => negb bdd depth x (* is this depth enough ?? *)
            | N na, N nb => 
                do na <- assoc Pos.eqb na (tmap bdd);
                do nb <- assoc Pos.eqb nb (tmap bdd);
                match na,nb with 
                  | (l1,v1,h1),(l2,v2,h2) =>
                      match NPeano.Nat.compare v1  v2 with 
                          | Eq =>
                              do x, bdd <- xorb bdd depth l1 l2;
                              do y, bdd <- xorb bdd depth h1 h2;
                              Some (mk_node bdd x v1 y)
                          | Lt =>
                              do x, bdd <- xorb bdd depth l1 b;
                              do y, bdd <- xorb bdd depth h1 b;
                              Some (mk_node bdd x v1 y)
                          | _ => 
                              do x, bdd <- xorb bdd depth a l2;
                              do y, bdd <- xorb bdd depth a h2;
                              Some (mk_node bdd x v2 y)
                end
          end
    end
       end.

  Definition var bdd x :=
    mk_node bdd F x T. 

  Fixpoint eval bdd depth env (a: expr) : option bool :=
    match depth with 
      | 0 => None
      | S depth => match a with 
                      | T => Some true
                      | F => Some false
                      | N n => do x <- assoc Pos.eqb n (tmap bdd);
                          match x with 
                            | (l,v,h) => 
                                do b <- List.nth_error env v;
                                if (b: bool) then eval bdd depth env h
                                else eval bdd depth env l
                          end
                  end
    end. 
          
End Inner.

Record BDD := 
  mk
    {
      content: Inner.BDD;
      depth: nat
    }.

Section t.   


Definition eval bdd env (a: expr) : option bool :=
  Inner.eval (content bdd) (depth bdd) env a. 

Definition andb bdd a b :=
  do e, r <- Inner.andb (content bdd) (depth bdd) a b;
  Some (e,mk r (depth bdd)).

Definition orb bdd a b :=
  do e, r <- Inner.orb (content bdd) (depth bdd) a b;
  Some (e,mk r (depth bdd)).

Definition negb bdd a  :=
  do e, r <- Inner.negb (content bdd) (depth bdd) a;
  Some (e, mk r (depth bdd)). 

Definition xorb bdd a b :=
  do e, r <- Inner.xorb (content bdd) (depth bdd) a b;
  Some (e,mk r (depth bdd)).

Definition ite bdd c l r:=
  do cl, bdd  <- andb bdd c l;
  do nc, bdd  <- negb bdd c;
  do ncr, bdd <- andb bdd nc r;
  orb bdd cl ncr.

Definition empty := mk Inner.empty 0.

Definition mk_var bdd x :=
  let (e, r) := Inner.var (content bdd) x in 
    (e, mk r (S (max x (depth bdd)))). 

End t. 

Definition test :=
  let bdd := empty in 
  let (a,bdd) := mk_var bdd 10 in 
  let (b,bdd) := mk_var bdd 11 in 
  do a,bdd <- orb bdd a b;
  do na,bdd <- negb bdd a;
  do r,bdd <- orb bdd a na;
  do nr,bdd <- negb bdd r;
  do nnr,bdd <- negb bdd nr;
  do x, bdd <- orb bdd nnr a;
  Some (r, bdd). 

Eval compute in test. 