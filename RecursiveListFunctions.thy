theory RecursiveListFunctions
imports Main
begin

fun cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "cat [] l = l" |
  "cat (h # T) l = h # (cat T l)"

fun tamanho :: "'a list \<Rightarrow> nat" where
  "tamanho [] = 0" |
  "tamanho (h # T) = 1 + tamanho T"

lemma tamanho_cat: "tamanho (cat L1 L2) = tamanho L1 + tamanho L2"
proof (induct L1)
  case Nil
  (* Caso base: L1 é a lista vazia [] *)
  show "tamanho (cat [] L2) = tamanho [] + tamanho L2"
  proof -
    have "cat [] L2 = L2" by simp
    moreover have "tamanho [] = 0" by simp
    ultimately show ?thesis by simp
  qed
next
  case (Cons h T)
  (* Passo indutivo: L1 = h # T *)
  assume IH: "tamanho (cat T L2) = tamanho T + tamanho L2"
  (* Queremos mostrar que: tamanho (cat (h # T) L2) = tamanho (h # T) + tamanho L2 *)
  show "tamanho (cat (h # T) L2) = tamanho (h # T) + tamanho L2"
  proof -
    have "cat (h # T) L2 = h # cat T L2" by simp
    moreover have "tamanho (h # cat T L2) = 1 + tamanho (cat T L2)" by simp
    moreover from IH have "tamanho (cat T L2) = tamanho T + tamanho L2" by simp
    ultimately have "tamanho (h # cat T L2) = 1 + tamanho T + tamanho L2" by simp
    moreover have "tamanho (h # T) = 1 + tamanho T" by simp
    ultimately show ?thesis by simp
  qed
qed

end