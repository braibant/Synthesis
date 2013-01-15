Require Import Common. 
Require TRS. 
Notation type2 := TRS.type2. 
Notation type1 := TRS.type1. 

Section expr. 
  (* Environement is the same in the whole expr *)
  Import TRS. 
  Inductive expr1' : list type2 ->  type1 -> Type :=
  | Elet : forall E F t t', pattern1 F t -> expr1' E t -> expr1' (E++F) t' -> expr1' E t'
  | Eprim : forall E args res (f : builtin args res), dlist  (fun t => expr1' E (T01 t)) args -> expr1' E (T01 res) 
  | Econstant : forall E (c : constant), expr1' E (T01 (cst_ty c))
  (* get a register of level 1 *)
  | Eget : forall E t (v : var E (Treg t)), expr1' E (t)
  (* get for input/output  *)
  | Eget_input  : forall E t (v : var E (Tinput t)), expr1' E (t)
  | Eget_output : forall E t (v : var E (Toutput t)), expr1' E (t)
                                                     
  (* TODO: Use Tenum instead of Tint *)
  | Eget_regfile : forall E size t (v : var E  (Tregfile size t)) n, expr1' E (T01 (Tint n)) -> expr1' E t
  | Efirst : forall E n t (v : var E (Tfifo n t)), expr1' E t
  | Eisfull : forall E n t (v : var E (Tfifo n t)), expr1' E (T01 Tbool)
  | Eisempty : forall E n t (v : var E (Tfifo n t)), expr1' E (T01 Tbool)
                                                    
  | Eunion : forall E {id fl} (case : expr1'_disjunct E fl), expr1' E (Tunion id fl)
  | Etuple : forall E l (v : dlist (expr1' E) l), expr1' E (Ttuple l)
  with expr1'_disjunct : list type2 -> list (ident * type1) -> Type :=
  | expr1'_disjunct_hd:forall E id t q, expr1' E t -> expr1'_disjunct E ((id,t) :: q) 
  | expr1'_disjunct_tl:forall E id t q, expr1'_disjunct E q -> expr1'_disjunct E ((id,t)::q) . 

  Inductive expr2 E : type2 -> Type :=
  | Eset : forall t, expr1' E t ->  expr2 E (Treg t)
  | Eset_regfile : forall size t n,
                     expr1' E (T01 (Tint n)) -> expr1' E t -> expr2 E (Tregfile size t) 
  (* operations on fifos *)
  | Epush : forall n t, expr1' E t -> expr2 E (Tfifo n t)
  | Epop  : forall n t, expr2 E (Tfifo n t) (* forgets the first element *)
  | Epushpop : forall n t, expr1' E t -> expr2 E (Tfifo n t)
  | Eclear : forall n t, expr2 E (Tfifo n t)

  (* set an output *)
  | Eset_output : forall t, expr1' E t -> expr2 E (Toutput t)
  (* do nothing *)
  | Enop : forall t, expr2 E t.
  
  Definition expr2_vector (E : list type2) := dlist (@expr2 E). 
End expr. 

Record rule mem :=
  mk_rule 
    {
      cond: expr1' mem (TRS.T01 Tbool);
      rhs : expr2_vector mem mem
    }.

Section i. 

Definition repl E t := match t with
                         | TRS.Treg t' => expr1' E t'
                         | _  => var E t
                       end. 


Fixpoint insert (t : type2) (G : list type2) (n : nat) {struct n} : list type2 :=
  match n with
    | O => t :: G
    | S n' => match G with
               | nil => t :: G
               | t' :: G' => t' :: insert t G' n'
             end
  end.

Fixpoint lift_var t G (x : var G t) t' n : var (insert t' G n) t :=
  match x with 
    | var_0 G' _ => 
        match n with 
          | 0 => var_S var_0
          | _ => var_0 
        end 
    | var_S G' _ t'' x'  => 
        match n with 
          | 0 => var_S (var_S x')
          | S n' => 
              (var_S (lift_var _ _ x' _ n') : var (insert t' (_ :: G') (S n')) t'')
        end
  end.
End i. 

Definition lift_expr1' : forall E t, TRS.expr1 E t -> expr1' E t. Admitted. 

Section t. 
  Variable mem : list type2. 

  Variable R : TRS.rule mem. 
  
  Definition S : rule mem.
  constructor. 

  (* map each variable from context G to a replacement that is valid in context G' *)
  Definition subst G G' := dlist (repl G') G. 

  Definition repl_0 E x : repl (x :: E) x. 
  Proof.
    unfold repl; destruct x; try apply var_0. apply Eget. apply var_0. 
  Defined. 
  
  Definition lift_expr E x a:   expr1' E x -> expr1' (a :: E) x. 
  Proof. 
  Admitted. 

  Definition lift_repl a E x  : repl E x -> repl (a :: E) x. 
  Proof. 
    unfold repl; destruct x; try apply (var_S). apply lift_expr.  
  Defined. 
  
  Definition subst_id : forall E, subst E E. 
  Proof. 
    unfold subst. 
    induction E. constructor.
    constructor.
    apply repl_0. 
  
    apply (dlist_map (lift_repl a E ) _ IHE).
  Defined. 

  Definition subst_compose : forall E F G, subst E F -> subst F G -> subst E G.
  Proof. 
    unfold subst. 
    intros. 
 
  Definition lifting_transformation E F  : (forall t, expr1' E t -> expr1' F t) -> forall t, repl E t -> repl F t. 
  Admitted. 
   
  eapply dlist_map. 
  2 : apply X. 
  apply lifting_transformation. 
  
  Definition map_subst t E F (s : subst E F) ( x : expr1' E t) :  expr1' F t. 
  induction x. 
  
  refine (let f := fix f t E F s x : expr1' F t :=
  match x with
    | Elet E F t t' patF expr body => _
    | Eprim E args res f x => _
    | Econstant E c =>  _ 
    | Eget E t v => _
    | Eget_input E t v => _
    | Eget_output E t v => _
    | Eget_regfile E size t v n x => _
    | Efirst E n t v => _
    | Eisfull E n t v => _
    | Eisempty E n t v => _
    | Eunion E id fl case => _
    | Etuple E l v => _
  end
          in f t E F s x). 
  admit. 
  apply Eprim. 
  intros. 
  induction X1. 
  
  Definition where_to_subst E F : TRS.where_clause E F -> subst F E. 
  induction 1.
  apply subst_id. 
  eapply subst_compose. apply IHX. 
 eapply dlist_map. 
 intros. 
 eapply lifting_transformation. 
  intros. 
eapply Elet.  apply p.
  apply lift_expr1'. apply e. apply X1. apply X0. apply subst_id. 
Defined. 
  apply lift_expr1'. 
  intros. 
  eapply Elet. 
  apply p. apply lift_expr1'. apply e. 
  auto.
  Defined.

  Definition abort_pattern2_vector E F :
    TRS.pattern2_vector E F -> 
    TRS.where_clause E F. 

  refine (let f := fix f E F (p : TRS.pattern2_vector E F) : TRS.where_clause E F :=
              match p with 
                | TRS.pattern2_vector_nil =>  _
                | TRS.pattern2_vector_cons E' F' t q 
                                       pat pats => 
                    _
              end
          in 
            f E F
              
         ).
  constructor. 
  auto. 
  Definition w_append : forall A B C, TRS.where_clause A B -> TRS.where_clause B C -> 
                                 TRS.where_clause A C. 
  Admitted. 
  apply f in pats. 
  
  Definition test : forall E t, TRS.pattern2 E t -> TRS.where_clause (t :: nil) E.  
  intros E t. 
  refine (fun X => match X with 
              TRS.Pvar2 t' =>  TRS.where_clause_nil _
            | TRS.Phole2 t' =>  _ 
            | TRS.Plift E' t'  p =>  _
          end
         ). 
  
  inversion pat;  subst; simpl. 
  
  
  simpl. 

eapply f in pats. 
  eapply w_append. 
  2: apply X. 

End t. 
  Fixpoint pattern2_vector_match E F (P : pattern2_vector E F ) : 
    eval_type2_list E -> option (eval_env eval_type2 F) :=
    match P with 
      | pattern2_vector_nil => fun _ => Some tt
      | pattern2_vector_cons E F t q p2Et p2vFq =>
          fun X => 
            let (A, B) := X in
              do X <- pattern2_match E t p2Et A;
              do Y <- pattern2_vector_match _ _ p2vFq B;
              Some (append_envs _ _  X Y)
    end. 
  
  Fixpoint where_clause_match {E F} (W : where_clause E F) {struct W}: 
    eval_type2_list E -> option (eval_type2_list F) :=
    match W with 
      | where_clause_nil _ => fun X => Some X
      | where_clause_cons E F G t pat exp w =>
          fun x =>
            do e <- eval_expr1' _ x t exp;
            do B <- pattern1_match F t pat e;
            where_clause_match w (append_envs _ _ x B  )
    end. 

  Definition eval_expr2_vector mem env (v : @expr2_vector env mem) : 
    eval_type2_list env -> eval_type2_list mem -> option (eval_type2_list mem) := 
    (fun ENV MEM =>  (dlist_fold _ _ _ (eval_expr2 _ ENV) mem v MEM)). 

  Definition eval_rule mem (r : rule mem) : relation (eval_type2_list mem) :=
    fun M1 M2 => 
      exists E, exists F,  (pattern2_vector_match _ _ (lhs r) M1 = Some E
           /\ where_clause_match (where_clauses _ r) E = Some F
           /\ eval_expr1' _ F _ (cond r) = Some true
           /\ eval_expr2_vector _ _ (rhs r) F M1 = Some M2). 
  
  Fixpoint eval_rules ty (l : list (rule ty)) : relation (eval_type2_list (ty)) :=
    match l with
      | nil => fun _ _ => True
      | cons t q => union (eval_rule ty t) (eval_rules ty q)
    end. 
  
  Definition eval_TRS T := eval_rules _ (trs_rules T). 
  
  Definition run_rule ty (r : rule ty) : eval_type2_list ty -> option (eval_type2_list ty) :=
    fun M1 => 
      do E <- pattern2_vector_match _ _ (lhs  r) M1;
      do F <- where_clause_match (where_clauses _ r) E;

      if (@eval_expr1' (env2  r) F _ (cond  r))
      then (@eval_expr2_vector _ _  (rhs  r) F M1)
      else None . 
  
  
  Fixpoint iter_option {A} n (f : A -> option A) x :=
    match n with 
      | 0 => Some x
      | S n => match f x with | None => Some x | Some x => iter_option n f x end 
    end. 
  
  Fixpoint first_rule {ty} (l : list (rule ty)) x :=
    match l with 
      | nil => Some x
      | cons t q => 
          match run_rule _ t x with 
            | None => first_rule q x
            | Some x => Some x 
          end
    end. 

  Fixpoint run_unfair n T x :=
    match n with 
      | 0 => Some x
    | S n => 
        match first_rule (trs_rules T) x with 
          | None => Some x
          | Some x => run_unfair n T x
        end
  end. 

  Notation "[]" := nil.
  Notation "a :: b" := (cons a b). 
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).
  Open Scope string_scope.
  
  Delimit Scope expr_scope with expr. 
  Notation "[| x , .. , z |]"  :=  (Etuple _ _ (dlist_cons x .. (dlist_cons z dlist_nil ).. )) (at level  0): expr_scope.

  
  Notation "{< f ; x ; y >}" := (Eprim _ _ _ (f) (dlist_cons  x (dlist_cons y dlist_nil))).

  Notation "{< f ; x >}" := (Eprim _ _ _ (f) (dlist_cons x dlist_nil)).

  Notation "~ x" :=  ({< BI_negb ; x >}) : expr_scope. 
  Notation "a || b" := ({< BI_orb ; a ; b >}) : expr_scope. 
  Notation "a - b" := ({< BI_minus _ ; a ; b >}) : expr_scope. 
  Notation "a + b" := ({< BI_plus _ ; a ; b >}) : expr_scope. 
  Notation "a = b" := ({< BI_eq _ ; a ; b >}) : expr_scope. 
  Notation "a < b" := ({< BI_lt _ ; a ; b >}) : expr_scope. 
  Notation "x <= y" := ((x < y) || (x = y))%expr : expr_scope. 
  Notation "x <> y" := (~(x = y))%expr : expr_scope. 
  Notation "! x" := (Eget _ _ x) (at level  10) : expr_scope . 
  Notation "[| x |]"  :=  (Etuple _ _ (dlist_cons x dlist_nil )) (at level  0): expr_scope.  
  Notation "{< x >}" := (Econstant _ x): expr_scope. 
  
  Delimit Scope pattern_scope with pattern.    
  Notation "[| x , .. , z |]" := (Ptuple _ _ (pattern_vector_cons _ _ _ _ x .. (pattern_vector_cons _ _ _ _ z pattern_vector_nil ).. )) (at  level 0): pattern_scope.  
  
  Notation "X 'of' u :: q " := ((X,u)::q) (at level 60, u at next level,  right associativity). 

  (* Notations for expr2 *)
  Delimit Scope expr2_scope with expr2. 
  Arguments Eset_regfile {E} size t n _%expr _%expr.  

  (* Arguments dlist_cons {T P} t q _ _ .  *)
  (* Arguments dlist_nil {T P}.  *)
  Notation "[| x , .. , z |]"  :=  ((dlist_cons x .. (dlist_cons  z (dlist_nil ) ).. )) (at level  0): expr2_scope.
  Notation "'[' key '<-' v ']' " := ( Eset_regfile  _ _ _  key v )(at level 0, no associativity) : expr2_scope.
  Notation "•" := (Enop _ _) : expr2_scope. 
  
  Definition mk_rule' {mem} env pat cond expr : rule mem :=
    mk_rule mem env env pat (where_clause_nil _ ) cond expr. 
