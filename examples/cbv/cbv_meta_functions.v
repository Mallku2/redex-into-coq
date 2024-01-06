Require Import 
        Coq.Strings.String
        Coq.Strings.Ascii
        Lists.List
        Lia.

Require Import
        patterns_terms
        patterns_terms_dec
        reduction
        lib_ext.ListExt
        lib_ext.tactics
        cbv_grammar.

Open Scope string_scope.

(* call-by-value lambda-calculus *)

(* we instantiate our language of patterns and terms, with the previous symbols *)
Import cbv_grammar.
Import CBVBase.
Import CallByValueTerms.
Import CallByValueTermsDec.

(* free-variables from a given lambda-term
   note that we just pay attention to the kind of terms produced
   by cbv_grammar, and do not consider contexts, since they do not appear
   as terms *)
Fixpoint fv (t : term) : list cnlit :=
  match t with
  | lit_term var                                  => 
      var :: nil
  | (|| (lit_term lamb) (|| (lit_term var) t' ||) ||) =>
      remove lit_eq_dec var (fv t')
  | (|| tl tr ||)  =>
      (fv tl) ++ (fv tr)
  | list_term_c l    => fv_lterm l
  | _                => nil
  end

with fv_lterm (l : list_term) : list cnlit :=
       match l with
       | nil_term_c       => nil
       | cons_term_c t l' => fv t ++ (fv_lterm l')
       end.

(* returns a fresh variable, different to any variable present in the provided
   list *)
Fixpoint fresh_var_list (l : list cnlit) : cnlit :=
  match l with
  | nil    => str "x"
  | y :: tl => 
      match fresh_var_list tl with
      | str z =>
          match lit_eq_dec y (str z) with
          | left _  => 
              (* we just modify z a little *)
              str (z ++ "'")
          | right _ =>
              (* y <> str z *)
              str z
          end
      | _    =>
          (* impossible case *)
          str "x"
      end
  end.

(* general mechanism to generate fresh variables, different to any bound variable 
   on a given term; requires a definition of free variables in a given term *)
Definition fresh_var (t : term) (fv : term -> list cnlit) : cnlit := 
  fresh_var_list (fv t).

(* capture-avoiding substitution meta-function: replaces a variable by another
   variable *)
Definition substitute_var (t_orig : term) (v v_subt : cnlit) : 
  {t : term | size_term t = size_term t_orig}.
  refine 
    (Fix
       (Wf_nat.well_founded_ltof _ (fun tvt : term * cnlit * cnlit =>
                                      size_term (fst (fst tvt))))
       (fun tvt => {t : term | size_term t = size_term (fst (fst tvt))})
       (* original term * variable to be replaced * replacement term *)
       (fun (tvt : term * cnlit * cnlit)
          (substitute' : 
            forall tvt' : term * cnlit * cnlit, 
              size_term (fst (fst tvt')) < size_term (fst (fst tvt)) -> 
              {t : term | size_term t = size_term (fst (fst tvt'))}) =>
          let t_orig  := fst (fst tvt) in
          let v       := snd (fst tvt) in
          let v_subst := snd tvt       in
          match t_orig as t' 
                return t_orig = t' -> {t : term | size_term t = size_term (fst (fst tvt))} with
          | lit_term (str s)                                   =>
              fun eqp : t_orig = lit_term (str s) =>
                match lit_eq_dec (str s) v with
                | left _  => exist _ t_orig _
                | right _ => exist _ (lit_term v_subst) _
                end
          | (|| (lit_term lamb) (|| (lit_term (str s)) t'' ||) ||) =>
              fun eqp : t_orig = (|| (lit_term lamb) (|| (lit_term (str s)) t'' ||) ||) =>
                match lit_eq_dec (str s) v with
                | left _  => 
                    (* {s == v}
                       no need to change t_orig *)
                    exist _ t_orig _
                | right _ => 
                    (* s <> v *)
                    match lit_eq_dec (str s) v_subst with
                    | left _ =>
                        (* capture could occur *)
                        (* we change the bounded variable by a fresh one *)
                        let fresh := fresh_var t'' fv in
                        let subst_t''_ev := substitute' (t'', str s, fresh) _ in
                        match subst_t''_ev as subt 
                              return subst_t''_ev = subt -> 
                                     {t : term | size_term t = size_term (fst (fst tvt))} with
                        | exist _ t''_subst ev_t'' =>
                            fun eqp_t'' : _ =>
                              let subst_t''_subst_ev := substitute' (t''_subst, v, v_subst) _ in
                              match subst_t''_subst_ev as subt' 
                                    return subst_t''_subst_ev = subt' -> 
                                           {t : term | size_term t = size_term (fst (fst tvt))} with
                              | exist _ t''' ev =>
                                  fun eqp_t''_subst : _ =>
                                    exist _ ((|| (lit_term lamb) (|| (lit_term fresh) t''' ||) ||)) _
                              end eq_refl
                        end eq_refl
                    | right _ =>
                        (* no risk of capture *)
                        match substitute' (t'', v, v_subst) _ with
                        | exist _ t''' ev =>
                            exist _ ((|| (lit_term lamb) (|| (lit_term (str s)) t''' ||) ||)) _
                        end
                    end
                end
          | (|| tl tr ||)                                        =>
              fun eqp : t_orig = (|| tl tr ||) =>
                let subst_tl_ev := substitute' (tl, v, v_subst) _ in
                let subst_tr_ev := substitute' (tr, v, v_subst) _ in
                match subst_tl_ev as ev_tl 
                      return subst_tl_ev = ev_tl -> {t : term | size_term t = size_term t_orig} with 
                | exist _ tl' ev_tl' =>
                    fun eqp_tl : _ =>
                      match subst_tr_ev as ev_tr 
                      return subst_tr_ev = ev_tr -> {t : term | size_term t = size_term t_orig} with
                      | exist _ tr' ev_tr' =>
                          fun eqp_tr : _ =>
                            exist _ ((|| tl' tr' ||)) _
                      end eq_refl 
                end eq_refl
          | _                                                =>
              fun eqp => exist _ t_orig _
          end eq_refl) (t_orig, v, v_subt)).
    all: 
      destruct tvt as [ [t' v'] v''];
      simpl;
      simpl in t_orig;
      assert(t' = t_orig) as Heq;
      [auto |];

      (rewrite Heq +
         (simpl in ev_tl';
          simpl in ev_tr'));

      rewrite eqp;

      solve [simpl;
             lia
            |simpl;
             simpl in ev;
             lia
            |reflexivity
            |simpl in ev;
             simpl in ev_t'';
             simpl;
             lia].

    Unshelve.
    all: 
      destruct tvt as [ [t' v'] v''];
      simpl;
      simpl in t_orig;
      assert(t' = t_orig) as Heq;
      [auto |];
      rewrite Heq;
      rewrite eqp;
      simpl;
      solve[lia
           |simpl in ev_t'';
            lia].
Defined.

(* general capture-avoiding substitution meta-function  *)
Definition substitute (t : term) (v : cnlit) (t' : term) : term.
  refine
    (Fix
       (Wf_nat.well_founded_ltof _ (fun tvt : term * cnlit * term =>
                                      size_term (fst (fst tvt))))
       (fun _ => term)
       (* original term * variable to be replaced * replacement term *)
       (fun (tvt : term * cnlit * term)
          (substitute' :
            forall tvt' : term * cnlit * term,
              size_term (fst (fst tvt')) < size_term (fst (fst tvt)) -> term) =>
          let t_orig  := fst (fst tvt) in
          let v       := snd (fst tvt) in
          let v_subst := snd tvt       in
           match t_orig as t' return t_orig = t' -> term with
           | lit_term (str s)                                   =>
               fun _ =>
                 match lit_eq_dec (str s) v with
                 | left _  => t'
                 | right _ => t
                 end
           | (|| (lit_term lamb) (|| (lit_term (str s)) t'' ||) ||) =>
               fun eqp : t_orig = (|| (lit_term lamb) (|| (lit_term (str s)) t'' ||) ||) =>
                 match lit_eq_dec (str s) v with
                 | left _  => t_orig
                 | right _ =>
                     (* s <> v *)
                     let fv_v_subst := fv v_subst in
                     match fv_v_subst with
                     | nil =>
                         (* no free-variables in v_subst: no risk of capture *)
                         (|| (lit_term lamb) (|| (lit_term (str s))
                                                 (substitute' (t'', v, v_subst) _) ||) ||)
                     | _   =>
                         (* check if s appears free in v_subst *)
                         match find (fun x => 
                                       match x with
                                       | str s' => String.eqb s' s
                                       | _      => false
                                       end) fv_v_subst with
                         | Some _ =>
                             (* s appears free in v_subst *)
                             let fresh := fresh_var_list (fv t'' ++ fv_v_subst) in
                             let t''_subst_ev := substitute_var t'' (str s) fresh in
                             match t''_subst_ev as t''_ev 
                                   return t''_subst_ev = t''_ev -> term with
                             | exist _ t''_subst ev_t'' =>
                                 fun eqp_t'' : _ =>
                                   (|| (lit_term lamb) (|| (lit_term fresh)
                                                           (substitute' 
                                                              (t''_subst, v, 
                                                                v_subst) _) ||) ||)
                             end eq_refl
                         | None =>
                             (* s does not appear free in t' *)
                             (|| (lit_term lamb) (|| (lit_term (str s))
                                                     (substitute' (t'', v, v_subst) _) ||) ||)
                         end
                     end
                 end
           | (|| tl tr ||)      =>
               fun eqp : t_orig = (|| tl tr ||) =>
                 (|| (substitute' (tl, v, v_subst) _) (substitute' (tr, v, v_subst) _) ||)
           | _                =>
               fun _ => t_orig
           end eq_refl) (t, v, t'));
    solve[destruct tvt as [ [t_orig' v'] v_subst'];
          simpl;
          simpl in t_orig;
          assert(t_orig = t_orig') as Heq;
          [reflexivity |];
          ((rewrite Heq in eqp) +
             (rewrite <- Heq));
          rewrite eqp;
          simpl;
          lia].
Defined.
