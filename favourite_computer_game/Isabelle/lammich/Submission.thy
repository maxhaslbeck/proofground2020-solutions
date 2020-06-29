theory Submission
imports Defs
begin


(* The append lemma - gives 30% of the points.
   Note: While this lemma gives less points, it's actually harder to prove! *)

lemma rle_append: "xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys \<Longrightarrow> rle (xs @ ys) = rle xs @ rle ys"
  apply (induction xs rule: rle.induct)
  apply (auto split: if_splits)
  subgoal by (metis (mono_tags, lifting) hd_Cons_tl takeWhile.simps(1) takeWhile.simps(2))
  subgoal
    by (metis (full_types) dropWhile.simps(1) dropWhile.simps(2) hd_Cons_tl)
  subgoal
    apply (cases ys)
    apply auto
    by (smt append_Nil2 last_in_set list.sel(1) rle.elims takeWhile.simps(2) takeWhile_append1 takeWhile_append2 takeWhile_eq_all_conv)
  subgoal
    apply (cases ys)
    apply auto
    by (smt append_Nil2 dropWhile_append1 dropWhile_append3 dropWhile_eq_Nil_conv last_appendR last_in_set list.sel(1) rle.elims takeWhile_dropWhile_id)
  done
(* Given the append lemma show the reverse lemma - gives 70% of the points.
   Note: While this lemma gives more points, it might actually be easier to prove *)
   
   
lemma [simp]: "set xs \<subseteq> {a} \<Longrightarrow> xs @ [a] = a # xs"   
  apply (induction xs)
  apply auto
  done
  
lemma SR: "set xs \<subseteq> {a} \<Longrightarrow> rev xs = xs"   
  apply (induction xs)
  apply auto
  done

lemma TKS: "set (takeWhile (\<lambda>y. y = x) xs) \<subseteq> {x}"  
  apply (induction xs)
  apply simp
  by (metis (mono_tags, lifting) set_takeWhileD singleton_iff subsetI)
  
   
lemma 1: "rle (rev xs) = rev (rle xs)"
proof (induction xs rule: rle.induct)
  case 1
  then show ?case by auto
next
  case (2 x xs)
  
  have 1: "[(x, Suc (length (takeWhile (\<lambda>y. y = x) xs)))] = rle (takeWhile (\<lambda>y. y = x) (x#xs))"
    apply (cases xs)
    apply auto
    by (metis rle.simps(1) self_append_conv takeWhile_dropWhile_id takeWhile_idem)
    
  have x1: "rev (takeWhile (\<lambda>y. y = x) xs) = takeWhile (\<lambda>y. y = x) xs"  
    by (simp add: SR[OF TKS])
    
  have x2: "rev (dropWhile (\<lambda>y. y = x) xs) @ takeWhile (\<lambda>y. y = x) (x # xs) = rev (x#xs)"
    apply simp
    apply (subst (3) takeWhile_dropWhile_id[of "(\<lambda>y. y = x)" xs, symmetric])
    apply (simp del: takeWhile_dropWhile_id)
    apply (subst x1)
    by (simp add: TKS)
  
  have "rev (rle (dropWhile (\<lambda>y. y = x) xs)) @ [(x, Suc (length (takeWhile (\<lambda>y. y = x) xs)))]
    = (rle (rev (x#xs)))
  "
    apply (simp only: 1 2[symmetric])
    apply (subst rle_append[symmetric])
    apply auto []
    apply (metis (full_types) append_Nil2 empty_iff filter_id_conv hd_dropWhile last_rev list.set(1) takeWhile_dropWhile_id takeWhile_eq_filter)
    apply (simp only: x2)
    done
    
    
  then show ?case
    by simp
  
qed
  

   
   
lemma rle_rev_if_rle_append: "(xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys \<Longrightarrow> rle (xs @ ys) = rle xs @ rle ys)
       \<Longrightarrow> rle (rev xs) = rev (rle xs)"
  using 1 by blast

end
