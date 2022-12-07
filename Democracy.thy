theory
  Democracy
imports
  MyNetwork
begin

datatype 'val msg
  = Propose (prop_val:'val)
  | Accept 'val

datatype ('val, 'proc) state
  = Nothing (* All procs begin in state Nothing *)
  | Value 'val (* Once a process receives an (Accept v) message, state changes to Value v *)
  | Vote_Count \<open>('proc \<Rightarrow> 'val option)\<close> (* Acceptor's state is Vote_Count f while election is occurring *)

fun initial_vote_count  where (* No votes counted yet *)
  \<open>initial_vote_count p = None\<close>

fun not_every_vote_counted  where (* true if there is a p in procs whose vote is not yet recorded *)
  \<open>not_every_vote_counted procs f = (\<exists>p\<in>procs.(f p = None\<and> p \<noteq> 0))\<close>

fun nonzero_counter where (* counts how many p in procs voted for a given val *)
  \<open>nonzero_counter procs f sval = card{p\<in> procs . f p = sval \<and> p\<noteq>0}\<close>

fun vals_with_votes where (* the set of values v for which some p in procs voted for v *)
  \<open>vals_with_votes procs f = {sv.(\<exists>p\<in>procs. f p = sv \<and> p \<noteq> 0)}\<close>

lemma only_some:
  assumes \<open>\<not>not_every_vote_counted procs f\<close>
  shows \<open>\<forall>sv.(sv\<in>(vals_with_votes procs f) \<longrightarrow> (\<exists>v. sv = Some v))\<close>
proof
  fix sv
  show \<open>sv\<in>(vals_with_votes procs f) \<longrightarrow> (\<exists>v. sv = Some v)\<close>
  proof
    assume h1:\<open>sv\<in>(vals_with_votes procs f)\<close>
    show \<open>\<exists>v. sv = Some v\<close>
    proof (rule ccontr)
      assume \<open>\<nexists>v. sv = Some v\<close>
      hence \<open>sv=None\<close> by auto
      moreover have \<open>\<exists>p\<in>procs. f p = sv \<and> p \<noteq> 0\<close>
        using h1 by auto
      ultimately have \<open>not_every_vote_counted procs f\<close> by auto
      thus \<open>False\<close> using assms by auto
    qed
  qed
qed

lemma counter1:
  assumes \<open>nonzero_counter procs f sv > 0\<close>
    (*and \<open>finite procs\<close>*)
  shows \<open> sv \<in> vals_with_votes procs f\<close>
proof -
  have \<open>card {p\<in>procs. (f p = sv \<and> p \<noteq> 0)}>0\<close>
    using assms by simp
  hence \<open>{p\<in>procs. (f p = sv \<and> p \<noteq> 0)} \<noteq> {}\<close>
    using card_gt_0_iff by blast
  from this obtain p where \<open>p\<in>procs\<and> f p = sv \<and> p\<noteq>0\<close> by auto
  thus ?thesis by auto
qed

lemma counter2:
  assumes \<open>sv \<in> vals_with_votes procs f\<close>
  assumes \<open>finite procs\<close>
  shows \<open>nonzero_counter procs f sv > 0\<close>
proof -
  have fin:\<open>finite {p\<in>procs. (f p = sv \<and> p \<noteq> 0)}\<close> using assms(2) by auto
  have \<open>(\<exists>p\<in>procs. (f p = sv \<and> p \<noteq> 0))\<close> using assms(1) by auto
  hence \<open>\<exists>sval. (sval\<in>{p\<in>procs. (f p = sv \<and> p \<noteq> 0)})\<close> by auto
  hence nonempty:\<open>{p\<in>procs. (f p = sv \<and> p \<noteq> 0)} \<noteq> {}\<close> by auto
  hence \<open>card{p\<in>procs. (f p = sv \<and> p \<noteq> 0)}>0\<close>
  proof(cases \<open>card{p\<in>procs. (f p = sv \<and> p \<noteq> 0)}\<close>)
    case 0
    hence \<open>{p\<in>procs. (f p = sv \<and> p \<noteq> 0)} = {}\<close>
      using card_0_eq fin by auto
    then show ?thesis using nonempty by auto
  next
    case (Suc nat)
    then show ?thesis by auto
  qed
  thus ?thesis by auto
qed

fun most_vote_counts where (* the highest number of votes received by any val *)
  \<open>most_vote_counts procs f = (Max ((nonzero_counter procs f)`(vals_with_votes procs f)))\<close>

lemma most:
  assumes \<open>\<not>(procs \<subseteq> {0})\<close>
    and \<open>finite procs\<close>
  shows \<open>most_vote_counts procs f > 0\<close>
proof -
  from assms(1) obtain p where \<open>p\<in>procs \<and> p\<noteq>0\<close> by auto
  hence fpin:\<open>f p \<in> vals_with_votes procs f\<close> by auto
  hence gz:\<open>nonzero_counter procs f (f p) > 0\<close> using counter2 assms(2) by simp
  have vfin:\<open>finite (vals_with_votes procs f)\<close> using assms(2) by auto
  have \<open>Max ((nonzero_counter procs f)`(vals_with_votes procs f))
                  \<ge> nonzero_counter procs f (f p)\<close>
    using fpin vfin by simp
  thus \<open>most_vote_counts procs f > 0\<close> using gz by auto
qed

fun set_of_potential_winners where (* the set of values which received the highest number of votes *)
  \<open>set_of_potential_winners procs f = {sv.(nonzero_counter procs f sv = most_vote_counts procs f)}\<close>

lemma potwinshavevotes:
  assumes \<open>\<not>(procs \<subseteq> {0})\<close>
    and \<open>finite procs\<close>
  shows \<open>set_of_potential_winners procs f \<subseteq> vals_with_votes procs f\<close>
proof
  fix x
  assume a:\<open>x \<in> set_of_potential_winners procs f\<close>
  show \<open>x \<in> vals_with_votes procs f\<close>
  proof -
    have \<open>nonzero_counter procs f x = most_vote_counts procs f\<close>
      using a by auto
    hence \<open>nonzero_counter procs f x > 0\<close>
      using most assms by simp
    thus \<open>x\<in>vals_with_votes procs f\<close> using counter1 by auto
  qed
qed

lemma potwinsaresome:
  assumes \<open>\<not>not_every_vote_counted procs f\<close>
    and \<open>\<not>(procs \<subseteq> {0})\<close>
    and \<open>finite procs\<close>
  shows \<open>sv\<in>(set_of_potential_winners procs f) \<Longrightarrow> (\<exists>v. (sv = Some v))\<close>
proof -
  assume \<open>sv\<in>(set_of_potential_winners procs f)\<close>
  hence \<open>sv\<in>(vals_with_votes procs f)\<close>
    using potwinshavevotes assms(2) assms(3) by (metis (mono_tags, lifting) in_mono)
  thus \<open>\<exists>v. sv = Some v\<close> using only_some assms(1) by auto
qed

fun pick_winner where (* picks a random winner from the set of potential winners *)
  \<open>pick_winner procs f = (SOME sv. sv \<in> (set_of_potential_winners procs f))\<close>

lemma pickerlemma:
  assumes \<open>A \<noteq> {}\<close>
  shows \<open>(SOME a. a \<in> A)\<in> A\<close>
  using assms some_in_eq by blast

lemma winnerispotential:
  assumes \<open>\<not>not_every_vote_counted procs f\<close>
    and \<open>\<not>(procs \<subseteq> {0})\<close>
    and \<open>finite procs\<close>
  shows \<open>(pick_winner procs f)\<in> (set_of_potential_winners procs f)\<close>
proof -
  from assms(2) obtain p where \<open>p\<in>procs \<and> p\<noteq>0\<close> by auto
  hence fpin:\<open>f p \<in> vals_with_votes procs f\<close> by auto
  hence valsnonempty:\<open>vals_with_votes procs f \<noteq> {}\<close>
    by auto
  have valsfinite:\<open>finite (vals_with_votes procs f)\<close>
    using assms(3) by auto
  hence maxin:\<open>(Max ((nonzero_counter procs f)`(vals_with_votes procs f)))
                      \<in> ((nonzero_counter procs f)`(vals_with_votes procs f))\<close>
    using valsnonempty valsfinite by simp
  moreover have \<open>(z\<in>((nonzero_counter procs f)`(vals_with_votes procs f))
              \<Longrightarrow> (\<exists>x.(x\<in>(vals_with_votes procs f) \<and> (z=nonzero_counter procs f x))))\<close>
    by auto
  hence \<open>\<exists>x.(x\<in>(vals_with_votes procs f) \<and> ((Max ((nonzero_counter procs f)`(vals_with_votes procs f)))=nonzero_counter procs f x))\<close>
    using maxin by auto
  (*from this obtain sv where \<open>sv\<in>(vals_with_votes procs f)
      \<and> (Max ((nonzero_counter procs f)`(vals_with_votes procs f))) = nonzero_counter procs f sv\<close>
    by auto*)
  hence \<open>(set_of_potential_winners procs f) \<noteq> {}\<close>
    by auto
  hence \<open>(SOME sv. sv \<in> (set_of_potential_winners procs f)) \<in> (set_of_potential_winners procs f)\<close>
    using pickerlemma[where ?A=\<open>set_of_potential_winners procs f\<close>] by auto
  thus ?thesis using pickerlemma by auto
qed

lemma winnersome:
  assumes \<open>\<not>not_every_vote_counted procs f\<close>
    and \<open>\<not>(procs \<subseteq> {0})\<close>
    and \<open>finite procs\<close>
  shows \<open>\<exists>v. (pick_winner procs f = Some v)\<close>
  using potwinsaresome[where ?sv=\<open>pick_winner procs f\<close>] winnerispotential assms by blast

fun set_value_and_send_accept_all where (* sets acceptor's state to Value v and sends (Accept v) to all p in procs *)
  \<open>set_value_and_send_accept_all procs v = (Value v,((\<lambda>p. (Send p (Accept v))) ` procs))\<close>

fun count_update where (* deals with incoming vote and updates acceptor's state. sends Accept messages if voting is completed *)
  \<open>count_update procs f sender val =
    (case (f sender) of
      None \<Rightarrow> (case (not_every_vote_counted procs (f (sender := Some val))) of
                  True \<Rightarrow> (Vote_Count (f (sender := Some val)), {}) |
                  False \<Rightarrow> (set_value_and_send_accept_all (procs\<union>{sender}) (the (pick_winner (procs\<union>{sender}) (f (sender := Some val)))))) |
      Some v \<Rightarrow> (Vote_Count f, {}))\<close>
(* f is the current vote count. This function is potentially called when the Acceptor receives (Propose val) from sender.
If the sender's vote has not yet been recorded, checks if there are other p in procs whose votes are not recorded either.
If there are others unrecorded, updates vote count to include sender's vote.
Otherwise, decides winner of election, sets state to Value (winner), and sends (Accept winner) to all p in procs.
(We use procs \<union> {sender} to decide election to avoid the case where procs \<subseteq> {0} which would lead to no votes.
This adjustment makes the case procs \<subseteq> {0} into the original ``first proposal received is accepted'' situation)
If the sender's vote has previously been recorded, does nothing. *)

fun acceptor_step where (* If Acceptor receives a vote, either initialize voting if it is the first vote,
                           Send (Accept v) if voting was already completed with winning value v,
                           or update Vote_Count if voting is ongoing.
                           For other events do nothing *)
  \<open>acceptor_step procs state (Receive sender (Propose val)) =
     (case state of
        Nothing   \<Rightarrow> (count_update procs initial_vote_count sender val) |
        Value v \<Rightarrow> (Value v, {Send sender (Accept v)}) |
        Vote_Count f \<Rightarrow> (count_update procs f sender val))\<close> |
  \<open>acceptor_step procs state _ = (state, {})\<close>

fun proposer_step where
  \<open>proposer_step procs Nothing (Request val) = (Nothing, {Send 0 (Propose val)})\<close> |
  \<open>proposer_step procs Nothing (Receive _ (Accept val)) = (Value val, {})\<close> |
  \<open>proposer_step procs state _ = (state, {})\<close>

fun consensus_step  where
  \<open>consensus_step procs proc =
     (if proc = 0 then acceptor_step procs else proposer_step procs)\<close>

(* Invariant 1: for any proposer p, if p's state is ``Value val'',
   then there exists a process that has sent a message
   ``Accept val'' to p. *)

definition inv1 where
  \<open>inv1 msgs states \<longleftrightarrow>
     (\<forall>proc val. proc \<noteq> 0 \<and> states proc = Value val \<longrightarrow>
                 (\<exists>sender. (sender, Send proc (Accept val)) \<in> msgs))\<close>

(* Invariant 2: if a message ``Accept val'' has been sent, then
   the acceptor is in the state ``Value val''. *)

definition inv2 where
  \<open>inv2 msgs states \<longleftrightarrow>
     (\<forall>sender recpt val. (sender, Send recpt (Accept val)) \<in> msgs \<longrightarrow>
                         states 0 = Value val)\<close>

(* Invariant 3: if a ``Propose val'' message has been sent, then the sender is not the Acceptor *)

definition inv3 where
  \<open>inv3 msgs \<longleftrightarrow> 
    (\<forall>sender recpt val. (sender, Send recpt (Propose val))\<in> msgs \<longrightarrow> sender\<noteq>0)\<close>

lemma invariant_propose:
  assumes \<open>msgs' = msgs \<union> {(proc, Send 0 (Propose val))}\<close>
    and \<open>inv1 msgs states \<and> inv2 msgs states\<close>
  shows \<open>inv1 msgs' states \<and> inv2 msgs' states\<close>
proof -
  have \<open>\<forall>sender proc val.
      (sender, Send proc (Accept val)) \<in> msgs' \<longleftrightarrow>
      (sender, Send proc (Accept val)) \<in> msgs\<close>
    using assms(1) by blast
  then show ?thesis
    by (meson assms(2) inv1_def inv2_def)
qed

lemma invariant3_accept:
  assumes \<open>msgs' = msgs \<union> {(proc, Send recpt (Accept val))}\<close>
    and \<open>inv3 msgs\<close>
  shows \<open>inv3 msgs'\<close>
proof -
  have \<open>\<forall>sender proc val.
      (sender, Send proc (Propose val)) \<in> msgs' \<longleftrightarrow>
      (sender, Send proc (Propose val)) \<in> msgs\<close>
    using assms(1) by blast
  then show ?thesis
  by (metis assms(2) inv3_def)
qed

lemma invariant3_empty: \<open>inv3 {}\<close>
proof -
  have \<open>\<forall>sender proc val. \<not>((sender, Send proc (Propose val))\<in>{})\<close>
    by simp
  thus ?thesis
  by (simp add: inv3_def)
qed
  
lemma invariant_decide:
  assumes \<open>states' = states (0 := Value val)\<close>
    and \<open>msgs' = msgs \<union> {(0, Send sender (Accept val))}\<close>
    and \<open>states 0 = Nothing \<or> states 0 = Value val\<close>
    and \<open>inv1 msgs states \<and> inv2 msgs states\<close>
  shows \<open>inv1 msgs' states' \<and> inv2 msgs' states'\<close>
proof -
  {
    fix p v
    assume asm: \<open>p \<noteq> 0 \<and> states' p = Value v\<close>
    hence \<open>states p = Value v\<close>
      by (simp add: asm assms(1))
    hence \<open>\<exists>sender. (sender, Send p (Accept v)) \<in> msgs\<close>
      by (meson asm assms(4) inv1_def)
    hence \<open>\<exists>sender. (sender, Send p (Accept v)) \<in> msgs'\<close>
      using assms(2) by blast
  }
  moreover {
    fix p1 p2 v
    assume asm: \<open>(p1, Send p2 (Accept v)) \<in> msgs'\<close>
    have \<open>states' 0 = Value v\<close>
    proof (cases \<open>(p1, Send p2 (Accept v)) \<in> msgs\<close>)
      case True
      then show ?thesis
      by (metis assms(1) assms(3) assms(4) fun_upd_same inv2_def state.distinct(1))
    next
      case False
      then show ?thesis
        using asm assms(1) assms(2) by auto
    qed
  }
  ultimately show ?thesis
    by (simp add: inv1_def inv2_def)
qed

lemma invariant_learn:
  assumes \<open>states' = states (proc := Value val)\<close>
    and \<open>(sender, Send proc (Accept val)) \<in> msgs\<close>
    and \<open>inv1 msgs states \<and> inv2 msgs states\<close>
  shows \<open>inv1 msgs states' \<and> inv2 msgs states'\<close>
proof -
  {
    fix p v
    assume asm: \<open>p \<noteq> 0 \<and> states' p = Value v\<close>
    have \<open>\<exists>sender. (sender, Send p (Accept v)) \<in> msgs\<close>
    proof (cases \<open>p = proc\<close>)
      case True
      then show ?thesis
        using asm assms(1) assms(2) by auto
    next
      case False
      then show ?thesis
        by (metis asm assms(1) assms(3) fun_upd_apply inv1_def)
    qed
  }
  moreover {
    fix p1 p2 v
    assume \<open>(p1, Send p2 (Accept v)) \<in> msgs\<close>
    hence \<open>states' 0 = Value v\<close>
      by (metis assms fun_upd_apply inv2_def)
  }
  ultimately show ?thesis
    by (simp add: inv1_def inv2_def)
qed

lemma invariant_proposer:
  assumes \<open>proposer_step procs (states proc) event = (new_state, sent)\<close>
    and \<open>msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)\<close>
    and \<open>states' = states (proc := new_state)\<close>
    and \<open>execute consensus_step (\<lambda>p. Nothing) procs (events @ [(proc, event)]) msgs' states'\<close>
    and \<open>inv1 msgs states \<and> inv2 msgs states\<close>
  shows \<open>inv1 msgs' states' \<and> inv2 msgs' states'\<close>
proof (cases event)
  case (Receive sender msg)
  then show ?thesis
  proof (cases msg)
    case (Propose val)
    then show ?thesis
      using Receive assms by auto
  next
    case (Accept val) (* proposer receives Accept message: learn the decided value *)
    then show ?thesis
    proof (cases \<open>states proc\<close>)
      case Nothing
      hence \<open>states' = states (proc := Value val) \<and> msgs' = msgs\<close>
        using Accept Receive assms(1) assms(2) assms(3) by auto
      then show ?thesis
        by (metis Accept Receive assms(4) assms(5) execute_receive invariant_learn)
    next
      case (Value v)
      then show ?thesis
        using assms by auto
    next
      case (Vote_Count f) (* A proposer should never be in this state *)
      then show ?thesis
      using assms(1) assms(2) assms(3) assms(5) by force
    qed
  qed
next
  (* on a Request event, proposer sends a Propose message if its state
     is None, or ignores the event if already learnt a decision *)
  case (Request val)
  then show \<open>inv1 msgs' states' \<and> inv2 msgs' states'\<close>
  proof (cases \<open>states proc\<close>)
    case Nothing
    hence \<open>states' = states \<and> msgs' = msgs \<union> {(proc, Send 0 (Propose val))}\<close>
      using Request assms(1) assms(2) assms(3) by auto
    then show ?thesis
      by (simp add: assms(5) invariant_propose)
  next
    case (Value v)
    then show ?thesis using assms by auto
  next
    case (Vote_Count f)
    then show ?thesis
    using assms(1) assms(2) assms(3) assms(5) by force
  qed
next
  case Timeout
  then show \<open>inv1 msgs' states' \<and> inv2 msgs' states'\<close>
    using assms by auto
qed

lemma flip_contrap: assumes \<open>\<not>P \<Longrightarrow> \<not> Q\<close> shows \<open>Q \<Longrightarrow> P\<close> using assms by auto

lemma invariant_acceptor:
  assumes \<open>acceptor_step procs (states 0) event = (new_state, sent)\<close>
    and \<open>msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)\<close>
    and \<open>states' = states (0 := new_state)\<close>
    and \<open>execute consensus_step (\<lambda>p. Nothing) procs (events @ [(0, event)]) msgs' states'\<close>
    and \<open>inv1 msgs states \<and> inv2 msgs states \<and> inv3 msgs\<close>
  shows \<open>inv1 msgs' states' \<and> inv2 msgs' states' \<and> inv3 msgs'\<close>
proof (cases event)
  case (Receive sender msg)
  then show \<open>inv1 msgs' states' \<and> inv2 msgs' states' \<and> inv3 msgs'\<close>
  proof (cases msg)
    case (Propose val)
    then show ?thesis
    proof (cases \<open>states 0\<close>)
      case Nothing
      then show ?thesis
      proof (cases \<open>not_every_vote_counted procs (initial_vote_count(sender:= Some val))\<close>)
        case True
        hence \<open>states' = states (0 := Vote_Count (initial_vote_count(sender:= Some val))) \<and> msgs' = msgs\<close>
        using Receive Propose Nothing True assms(1) assms(2) assms(3) by auto
        then show ?thesis
        by (smt (z3) Nothing assms(5) fun_upd_apply inv1_def inv2_def state.distinct(1))
      next
        case False
        hence hy:\<open>not_every_vote_counted procs (initial_vote_count(sender:= Some val)) = False\<close> by auto
        moreover have \<open>event = Receive sender (Propose val)\<close>
          by (simp add: Propose Receive)
        hence thiscase:\<open>(acceptor_step procs (states 0) event) = (acceptor_step procs Nothing (Receive sender (Propose val)))\<close>
          using Nothing by simp
        hence ha:\<open>sent =snd (acceptor_step procs Nothing (Receive sender (Propose val)))\<close>
          using assms(1) by (smt (verit, best) sndI)
        have h:\<open>acceptor_step procs Nothing (Receive sender (Propose val))
                       = count_update procs initial_vote_count sender val\<close> by simp
        have hh:\<open>initial_vote_count sender = None\<close> by simp
        let ?w=\<open>(the (pick_winner (procs\<union>{sender}) (initial_vote_count (sender := Some val))))\<close>
        have hz:\<open>count_update procs initial_vote_count sender val = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close>
          apply (simp only: count_update.simps hh hy)
          by simp
        have hw:\<open>set_value_and_send_accept_all (procs\<union>{sender}) ?w = (Value ?w,((\<lambda>p. (Send p (Accept ?w))) ` (procs\<union>{sender})))\<close>
          by simp
        hence sentis:\<open>sent = ((\<lambda>p. (Send p (Accept ?w))) ` (procs\<union>{sender}))\<close> using ha h hz hw by simp
        hence \<open>\<forall>x\<in>sent. send_msg x = (Accept ?w)\<close>
        by force
        moreover have \<open>send_msg (Send 0 (Propose val))\<noteq> (Accept ?w)\<close>
        by (metis msg.distinct(1) send.sel(2))
        moreover have \<open>(sender, Send 0 (Propose val))\<in> msgs'\<close>
          using Propose Receive assms(4) by auto
        hence \<open>(sender, Send 0 (Propose val))\<in> msgs\<close>
        using assms(2) calculation(2) calculation(3) by blast
        hence nonzero:\<open>sender\<noteq>0\<close>
        by (meson assms(5) inv3_def)
        have theprocs:\<open>\<forall>p\<in>procs. p=0\<or>p=sender\<close>
        using hy by fastforce
        hence theprocscont:\<open>(procs\<union>{sender})\<subseteq>{0,sender}\<close> by blast
        hence pexist:\<open>\<exists>p\<in>(procs\<union>{sender}). (((initial_vote_count(sender:= Some val)) p) = (Some val) \<and> p \<noteq> 0)\<close>
          using nonzero by auto
        hence \<open>Some val \<in> {v.\<exists>p\<in>(procs\<union>{sender}). (((initial_vote_count(sender:= Some val)) p) = v \<and> p \<noteq> 0)}\<close>
          by simp
        hence valin:\<open>Some val \<in> vals_with_votes (procs\<union>{sender}) (initial_vote_count(sender:= Some val))\<close>
          by auto
        moreover have \<open>\<exists>p\<in>(procs\<union>{sender}). (((initial_vote_count(sender:= Some val)) p) = v \<and> p \<noteq> 0)\<longrightarrow>v=Some val\<close>
          by simp
        hence \<open>{v.\<exists>p\<in>(procs\<union>{sender}). (((initial_vote_count(sender:= Some val)) p) = v \<and> p \<noteq> 0)}\<subseteq> {Some val}\<close>
          using theprocs by auto
        hence knowvalswithvotes:\<open>vals_with_votes (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) = {Some val}\<close>
          by (smt (z3) Collect_cong valin empty_iff subset_singleton_iff vals_with_votes.elims)
        hence \<open>sender\<in>{p\<in> (procs\<union>{sender}) . ((initial_vote_count(sender:= Some val)) p = (Some val) \<and> p\<noteq>0)}\<close>
        using theprocs by fastforce
        hence somevalcount:\<open>nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) (Some val) =1\<close>
          using pexist by simp
        hence \<open>(nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)))`(vals_with_votes (procs\<union>{sender}) (initial_vote_count(sender:= Some val))) = {1}\<close>
          by (metis knowvalswithvotes image_insert image_is_empty)
        hence mostvotes1:\<open>most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) = 1\<close> by simp
        hence \<open>nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) (Some val) = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some val))\<close>
          using somevalcount by linarith
        hence somevalcontainment:\<open>Some val \<in> set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some val))\<close>
          by simp
        moreover have \<open>\<And>somev.(somev\<noteq> Some val \<longrightarrow> {p\<in> (procs\<union>{sender}) . ((initial_vote_count(sender:= Some val)) p = somev \<and> p\<noteq>0)} = {})\<close>
          using theprocs by fastforce
        hence \<open>\<And>somev.(somev\<noteq> Some val \<longrightarrow> card{p\<in> (procs\<union>{sender}) . ((initial_vote_count(sender:= Some val)) p = somev \<and> p\<noteq>0)} =0)\<close>
          by (metis (no_types, lifting) card.empty)
        hence \<open>\<And>somev.(somev\<noteq> Some val \<longrightarrow> nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) somev =0)\<close>
          by simp
        hence conp:\<open>\<And>somev.(somev \<noteq> Some val \<longrightarrow> nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) somev \<noteq> most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some val)))\<close>
          using mostvotes1 by simp
        hence conp2:\<open>\<And>somev.(\<not>(somev = Some val) \<Longrightarrow> \<not>(nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) somev = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some val))))\<close>
          by auto
        hence \<open>\<And>somev.((nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) somev = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some val))) \<Longrightarrow> somev=Some val)\<close>
          using flip_contrap by blast
        hence cont:\<open>\<And>somev.((nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) somev = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some val))) \<Longrightarrow> somev\<in>{Some val})\<close>
          by blast
        have \<open>set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) \<subseteq> {Some val}\<close>
        proof
          fix x
          assume as:\<open>x\<in> set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some val))\<close>
          hence \<open>x\<in>{some.(nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) some = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some val)))}\<close>
            by simp
          hence \<open>(nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) x = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some val)))\<close>
            by simp
          thus \<open>x\<in>{Some val}\<close> using cont
          by blast
        qed
        hence \<open>set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) = {Some val}\<close>
          using somevalcontainment by fastforce
        hence simper:\<open>{Some val} = set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some val))\<close>
          by auto
        moreover have \<open>(SOME v. v \<in> {Some val}) = Some val\<close>
          by simp
        hence \<open>(SOME v. v \<in> set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some val))) = Some val\<close>
          using simper by simp
        hence \<open>pick_winner (procs\<union>{sender}) (initial_vote_count(sender:= Some val)) = Some val\<close>
          by simp
        hence valwins:\<open>the (pick_winner (procs\<union>{sender}) (initial_vote_count(sender:= Some val))) = val\<close>
          by auto
        hence exactsent:\<open>sent = ((\<lambda>p. (Send p (Accept val))) ` (procs\<union>{sender}))\<close>
          using sentis by simp
        hence \<open>msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` ((\<lambda>p. (Send p (Accept val))) ` (procs\<union>{sender})))\<close>
          using assms(2) by simp
        hence knowmsgs1:\<open>msgs' = msgs \<union> ((\<lambda>p. (0,(Send p (Accept val)))) ` (procs\<union>{sender}))\<close>
          by auto
        hence knowmsgs2:\<open>msgs'\<subseteq> msgs\<union> {(0, (Send sender (Accept val))),(0,(Send 0 (Accept val)))}\<close>
          using theprocscont by auto
        hence knowinv3:\<open>inv3 msgs'\<close>
        by (metis (no_types, lifting) Un_insert_right assms(5) inv3_def invariant3_accept subsetD sup_bot_right)
        moreover have knowstates:\<open>states' = states (0 := Value val)\<close>
          by (metis Pair_inject thiscase valwins assms(1) assms(3) h hw hz)
        hence knowinv1: \<open>inv1 msgs' states'\<close>
          using knowmsgs1 knowmsgs2 by (smt (z3) Nothing assms(5) fun_upd_apply inv1_def inv2_def state.distinct(1))
        have \<open>\<forall>s r v. (s, Send r (Accept v)) \<notin> msgs\<close>
          using assms(5) Nothing by (simp add: inv2_def)
        hence knowinv2:\<open>inv2 msgs' states'\<close>
          using knowmsgs2 knowstates assms(5) Nothing inv1_def inv2_def
        by (smt (verit) Pair_inject UnE fun_upd_apply insertE msg.inject(2) send.inject singletonD subset_eq)
        thus ?thesis using knowinv1 knowinv2 knowinv3
          by auto
      qed
    next
      case (Value val') (* already decided previously *)
      hence \<open>states' = states \<and>
             msgs' = msgs \<union> {(0, Send sender (Accept val'))}\<close>
        using Receive Propose assms(1) assms(2) assms(3) by auto
      then show ?thesis
        by (metis Value assms(3) assms(5) fun_upd_same invariant3_accept invariant_decide)
    next
      case (Vote_Count f)
      then show ?thesis
      proof (cases \<open>f sender = None\<close>)
        case True
        then show ?thesis
        proof (cases \<open>not_every_vote_counted procs (f(sender:= Some val))\<close>)
          case True
          hence hy:\<open>not_every_vote_counted procs (f(sender:= Some val)) = True\<close> by auto
          have thiscase:\<open>(acceptor_step procs (states 0) event) = (acceptor_step procs (Vote_Count f) (Receive sender (Propose val)))\<close>
            using Vote_Count Receive Propose by simp
          hence ha:\<open>sent =snd (acceptor_step procs (Vote_Count f) (Receive sender (Propose val)))\<close>
            using assms(1) by (smt (verit, best) sndI)
          have h:\<open>acceptor_step procs (Vote_Count f) (Receive sender (Propose val))
                         = count_update procs f sender val\<close> by simp
          have hz:\<open>count_update procs f sender val = (Vote_Count (f(sender:=Some val)),{})\<close>
            apply (simp only: count_update.simps hy \<open>f sender=None\<close>)
            by simp
          hence emptysent:\<open>sent={}\<close> using Vote_Count assms(1)
            using ha by auto
          hence knowmsgs:\<open>msgs'=msgs\<close> using assms(2)
            by auto
          have knowstates:\<open>states' = states (0 := Vote_Count (f(sender:= Some val)))\<close>
            using Vote_Count True assms(1) assms(3) \<open>f sender=None\<close> thiscase by auto
          hence \<open>states' = states (0 := Vote_Count (f(sender:= Some val))) \<and> msgs' = msgs\<close>
            using knowmsgs knowstates by auto
          thus ?thesis
            by (metis (no_types, lifting) Vote_Count assms(5) fun_upd_other inv1_def inv2_def state.distinct(5))
        next
          case False
          hence hy:\<open>not_every_vote_counted procs (f(sender:= Some val)) = False\<close> by auto
          let ?w=\<open>(the (pick_winner (procs\<union>{sender}) (f (sender := Some val))))\<close>
          have thiscase:\<open>(acceptor_step procs (states 0) event) = (acceptor_step procs (Vote_Count f) (Receive sender (Propose val)))\<close>
            using Vote_Count Receive Propose by simp
          hence ha:\<open>sent =snd (acceptor_step procs (Vote_Count f) (Receive sender (Propose val)))\<close>
            using assms(1) by (smt (verit, best) sndI)
          have h:\<open>acceptor_step procs (Vote_Count f) (Receive sender (Propose val))
                         = count_update procs f sender val\<close> by simp
          have hz:\<open>count_update procs f sender val = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close>
            apply (simp only: count_update.simps hy \<open>f sender=None\<close>)
            by simp
          have hw:\<open>set_value_and_send_accept_all (procs\<union>{sender}) ?w = (Value ?w,((\<lambda>p. (Send p (Accept ?w))) ` (procs\<union>{sender})))\<close>
            by simp
          hence sentis:\<open>sent = ((\<lambda>p. (Send p (Accept ?w))) ` (procs\<union>{sender}))\<close> using ha h hz hw by simp
          hence exactsent:\<open>sent = ((\<lambda>p. (Send p (Accept ?w))) ` (procs\<union>{sender}))\<close>
            using sentis by simp
          hence \<open>msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` ((\<lambda>p. (Send p (Accept ?w))) ` (procs\<union>{sender})))\<close>
            using assms(2) by simp
          hence knowmsgs:\<open>msgs' = msgs \<union> ((\<lambda>p. (0,(Send p (Accept ?w)))) ` (procs\<union>{sender}))\<close>
            by blast
          hence knowinv3:\<open>inv3 msgs'\<close>
            by (smt (verit) Pair_inject UnE assms(5) image_iff inv3_def msg.distinct(1) send.inject)
          moreover have knowstates:\<open>states' = states (0 := Value ?w)\<close>
            using thiscase by (metis Pair_inject assms(1) assms(3) h hw hz)
          hence knowinv1: \<open>inv1 msgs' states'\<close>
            using knowmsgs assms(5)
            by (metis (no_types, lifting) Vote_Count fun_upd_apply inv1_def inv2_def state.distinct(5))
          have \<open>\<forall>s r v. (s, Send r (Accept v)) \<notin> msgs\<close>
            using assms(5) Vote_Count by (simp add: inv2_def)
          hence knowinv2:\<open>inv2 msgs' states'\<close>
            using knowmsgs knowstates assms(5) Vote_Count inv1_def
            by (simp add: image_iff inv2_def)
          thus ?thesis using knowinv1 knowinv2 knowinv3
            by auto
        qed
      next
        case False
        hence vexist:\<open>\<exists>v.(f sender = Some v)\<close>
          by auto
        have thiscase:\<open>(acceptor_step procs (states 0) event) = (acceptor_step procs (Vote_Count f) (Receive sender (Propose val)))\<close>
          using Vote_Count Receive Propose by simp
        hence ha:\<open>sent =snd (acceptor_step procs (Vote_Count f) (Receive sender (Propose val)))\<close>
          using assms(1) by (smt (verit, best) sndI)
        have h:\<open>acceptor_step procs (Vote_Count f) (Receive sender (Propose val))
                       = count_update procs f sender val\<close> by simp
        have hz:\<open>count_update procs f sender val = (Vote_Count f,{})\<close>
          apply (simp only: count_update.simps)
        using vexist by auto
        hence emptysent:\<open>sent={}\<close> using Vote_Count assms(1)
          using ha by auto
        hence knowmsgs:\<open>msgs'=msgs\<close> using assms(2)
          by auto
        have \<open>states' = states (0 := Vote_Count f)\<close>
          using assms(1) assms(3) hz thiscase by auto
        hence knowstates:\<open>states' = states\<close>
          using Vote_Count by auto
        hence \<open>states' = states \<and> msgs' = msgs\<close>
          using knowmsgs knowstates by auto
        thus ?thesis
          by (metis (no_types, lifting) assms(5))
      qed
    qed
  next
    case (Accept val)
    then show ?thesis
      using Receive assms by auto
  qed
next
  case (Request val)
  then show ?thesis
    using assms by auto
next
  case Timeout
  then show ?thesis
    using assms by auto
qed

lemma invariants:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs' states'\<close>
  shows \<open>inv1 msgs' states' \<and> inv2 msgs' states'\<and> inv3 msgs'\<close>
using assms proof(induction events arbitrary: msgs' states' rule: List.rev_induct)
  case Nil
  from this show \<open>inv1 msgs' states' \<and> inv2 msgs' states'\<and> inv3 msgs'\<close>
    using execute_init inv1_def inv2_def inv3_def by fastforce
next
  case (snoc x events)
  obtain proc event where \<open>x = (proc, event)\<close>
    by fastforce
  hence exec: \<open>execute consensus_step (\<lambda>p. Nothing) procs
               (events @ [(proc, event)]) msgs' states'\<close>
    using snoc.prems by blast
  from this obtain msgs states sent new_state
    where step_rel1: \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
      and step_rel2: \<open>consensus_step procs proc (states proc) event = (new_state, sent)\<close>
      and step_rel3: \<open>msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)\<close>
      and step_rel4: \<open>states' = states (proc := new_state)\<close>
    by auto
  have inv_before: \<open>inv1 msgs states \<and> inv2 msgs states\<and> inv3 msgs\<close>
    using snoc.IH step_rel1 by fastforce
  then show \<open>inv1 msgs' states' \<and> inv2 msgs' states'\<and> inv3 msgs'\<close>
  proof (cases \<open>proc = 0\<close>)
    case True
    then show ?thesis
    by (metis consensus_step.elims exec invariant_acceptor snoc.IH step_rel1 step_rel2 step_rel3 step_rel4)
  next
    case False
    hence h:\<open>inv1 msgs' states' \<and> inv2 msgs' states'\<close>
      by (metis consensus_step.simps exec inv_before invariant_proposer
          step_rel2 step_rel3 step_rel4)
    have \<open>inv3 msgs'\<close>
      by (smt (verit) False Un_iff exec execute_step image_iff inv3_def prod.inject snoc.IH)
    thus ?thesis using h by auto
  qed
qed

theorem agreement:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
    and \<open>states proc1 = Value val1\<close> and \<open>states proc2 = Value val2\<close>
  shows \<open>val1 = val2\<close>
proof -
  have \<open>states 0 = Value val1\<close>
    by (metis assms(1) assms(2) inv1_def inv2_def invariants)
  moreover have \<open>states 0 = Value val2\<close>
    by (metis assms(1) assms(3) inv1_def inv2_def invariants)
  ultimately have \<open>Value val1 = Value val2\<close>
    by simp
  thus \<open>val1=val2\<close> by auto
qed

(* The theorem shows that consensus_step indeed yields consensus.
   Let us now verify that the election process is valid. First we define and verify a function
   to identify the vote cast by each process. *)

fun is_received_vote where (* recognizes whether an event is a vote from the given proc *)
  \<open>is_received_vote proc (_, (Receive p (Propose _))) = (p=proc)\<close> |
  \<open>is_received_vote proc _ = False\<close>

fun find_vote where (* Tells us which value was the first vote received from the given proc *)
  \<open>find_vote [] proc = None\<close> |
  \<open>find_vote (x#xs) proc = (case (is_received_vote proc x) of
        True   \<Rightarrow> Some (prop_val (recv_msg (snd x))) |
        False \<Rightarrow> find_vote xs proc)\<close>

lemma find_vote_lemma:
  fixes p
  assumes \<open>find_vote x p = find_vote y p\<close>
  shows \<open>find_vote (a # x) p = find_vote (a # y) p\<close>
proof -
  have \<open>find_vote (a # x) p = (case (is_received_vote p a) of
        True   \<Rightarrow> Some (prop_val (recv_msg (snd a))) |
        False \<Rightarrow> find_vote x p)\<close> by auto
  moreover have \<open>(case (is_received_vote p a) of
        True   \<Rightarrow> Some (prop_val (recv_msg (snd a))) |
        False \<Rightarrow> find_vote y p) = find_vote (a # y) p\<close> by auto
  ultimately show ?thesis
  using assms by presburger
qed

lemma find_vote_lemma1:
  fixes p
  shows \<open>find_vote x p = Some val \<longrightarrow> find_vote (x @ [a]) p = Some val\<close>
proof (induct x)
  case Nil
  hence \<open>find_vote Nil p = None\<close>
    by simp
  then show ?case by auto
next
  case (Cons b x)
  then show ?case
  proof (cases \<open>is_received_vote p b\<close>)
    case True
    hence \<open>find_vote (b # x) p = Some (prop_val (recv_msg (snd b)))\<close>
      by auto
    moreover have \<open>find_vote ((b # x)@[a]) p = Some (prop_val (recv_msg (snd b)))\<close>
      by (simp add: True)
    ultimately show ?thesis by auto
  next
    case False
    hence \<open>find_vote (b # x) p = find_vote x p\<close>
      by auto
    moreover have \<open>find_vote ((b # x)@[a]) p = find_vote (x@[a]) p\<close>
      by (simp add: False)
    then show ?thesis
      using calculation local.Cons by presburger
  qed
qed

lemma find_vote_lemma1b:
  assumes \<open>find_vote x p = Some val\<close>
  shows \<open>find_vote (x @ [a]) p = Some val\<close>
  using find_vote_lemma1 by (metis assms)

lemma find_vote_lemma2:
  assumes \<open>find_vote x = find_vote y\<close>
  shows \<open>find_vote (a # x) = find_vote (a # y)\<close>
proof
  fix p
  show \<open>find_vote (a # x) p = find_vote (a # y) p\<close>
    using find_vote_lemma by (metis assms)
qed

lemma find_vote_lemma3pre:
  assumes \<open>find_vote x p = None\<close>
  shows \<open>find_vote (x @ y) p = find_vote y p\<close>
  using assms
proof (induct x)
  case Nil
  then show ?case by auto
next
  case (Cons a x)
  have notvote:\<open>\<not>is_received_vote p a\<close>
  proof(rule ccontr)
    assume \<open>\<not>\<not>is_received_vote p a\<close>
    hence \<open>is_received_vote p a\<close> by auto
    hence \<open>find_vote (a # x) p = Some (prop_val (recv_msg (snd a)))\<close>
      by auto
    thus \<open>False\<close> using \<open>find_vote (a # x) p = None\<close> by auto
  qed
  hence \<open>find_vote (a # x) p = find_vote x p\<close> by auto
  hence \<open>find_vote x p = None\<close>
    using \<open>find_vote (a # x) p = None\<close> by simp
  hence \<open>find_vote (x @ y) p = find_vote y p\<close>
    using \<open>find_vote x p = None \<Longrightarrow> find_vote (x @ y) p = find_vote y p\<close> by auto
  hence \<open>find_vote ((a # (x@y))) p = find_vote (a # y) p\<close>
    using find_vote_lemma[where ?x=\<open>x @ y\<close> and ?y=y] by auto
  moreover have \<open>find_vote (a # y) p = find_vote y p\<close> using notvote by auto
  ultimately show ?case by auto
qed

lemma find_vote_lemma3wtftype:
  assumes \<open>find_vote (x :: ('proc \<times> ('proc, 'val msg, 'val) event) list) (p :: 'proc) = None\<close>
  shows \<open>find_vote (x @ [(a :: 'proc \<times> ('proc, 'val msg, 'val) event)]) p = find_vote [a] p\<close>
  using assms find_vote_lemma3pre[where ?y=\<open>[a]\<close> and ?x = x and ?p = p] by simp

lemma find_vote_lemma3type:
  assumes \<open>find_vote (x :: ('proc \<times> ('proc, 'val msg, 'val) event) list) (p :: 'proc) = None\<close>
  shows \<open>find_vote (x @ [(q, event :: ('proc, 'val msg, 'val) event)]) p = find_vote [(q,event)] p\<close>
  using find_vote_lemma3wtftype assms by auto

(*
lemma find_vote_lemma3:
  assumes \<open>find_vote x p = None\<close>
  shows \<open>find_vote (x @ [(0,event)]) p = find_vote [(0,event)] p\<close>
  using  find_vote_lemma3type[where ?x=x  and ?p = p and ?q=0 and ?event=event] assms by metis

lemma find_vote_lemma3:
  assumes \<open>find_vote x p = None\<close>
  shows \<open>find_vote (x @ [(0,event)]) p = find_vote [(0,event)] p\<close>
  using  find_vote_lemma3wtf[where ?a=\<open>(0,event)\<close> and ?x = x and ?p = p] assms by auto
*)





(* note: find_vote events : 'proc \<Rightarrow> 'val option is the actual record of votes cast *)

(* Invariant 4: if the acceptor is in state ``Value val'' then val is a valid winner,
                or procs \<subseteq> {0} (in which case there is no election) *)

definition inv4 where
  \<open>inv4 procs events states \<longleftrightarrow>
     ((\<forall>val.(states 0 = Value val \<longrightarrow>
                 (Some val \<in> set_of_potential_winners procs (find_vote events))))\<or>(procs \<subseteq> {0}))\<close>

(* Invariant 5: if the acceptor is in state ``Value val'' then voting is done. *)

definition inv5 where
  \<open>inv5 procs events states \<longleftrightarrow>
     (\<forall>val.(states 0 = Value val \<longrightarrow>
                 (\<not>(not_every_vote_counted procs (find_vote events)))))\<close>

(* Invariant 6: if the acceptor is in state ``Vote_Count f'' then f = (find_vote events),
                that is, f is indeed tracking the votes cast. *)

definition inv6 where
  \<open>inv6 procs events states \<longleftrightarrow>
     (\<forall>f.(states 0 = Vote_Count f \<longrightarrow>
                 (f= (find_vote events)\<and> (not_every_vote_counted procs (find_vote events)))))\<close>

(* Invariant 7: if a message (sender, Send p (Propose val)) is in msgs, then p=0 *)

definition inv7 where
  \<open>inv7 msgs \<longleftrightarrow>
     (\<forall>p sender val.((sender, Send p (Propose val))\<in>msgs \<longrightarrow>
                 (p=0)))\<close>

(* Invariant 8: if the acceptor is in state Nothing then find_vote events = initial_vote_count *)

definition inv8 where
  \<open>inv8 events states \<longleftrightarrow>
     (states 0 = Nothing \<longrightarrow>
                 (find_vote events=initial_vote_count))\<close>

lemma inv456initial:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs [] msgs states\<close>
  shows \<open>inv4 procs [] states \<and> inv5 procs [] states \<and> inv6 procs [] states\<close>
proof -
  have \<open>states = (\<lambda>x. Nothing)\<close>
    using assms execute_init by blast
  thus ?thesis
    using inv4_def inv5_def inv6_def by (metis state.distinct(1) state.distinct(3))
qed

lemma inv7initial: \<open>inv7 {}\<close>
  using inv7_def by blast

lemma inv8initial: \<open>inv8 [] states\<close>
proof -
  have \<open>find_vote []=initial_vote_count\<close> by auto
  thus ?thesis using inv8_def by blast
qed

lemma anotherinv7:
  assumes \<open>inv7 msgs\<close>
    and \<open>msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)\<close>
    and \<open>execute consensus_step (\<lambda>x. Nothing) procs (events @ [(proc,event)]) msgs' states'\<close>
    and \<open>consensus_step procs proc (states proc) event = (new_state, sent)\<close>
    and \<open>states' = states(proc:=new_state)\<close>
  shows \<open>inv7 msgs'\<close>
proof (cases event)
  case (Receive sender msg)
  show ?thesis
  proof (cases \<open>proc=0\<close>)
    case True
    hence know:\<open>(new_state,sent) = acceptor_step procs (states proc) (Receive sender msg)\<close>
      using assms(4) Receive acceptor_step.elims by force
    hence knowsent:\<open>sent = snd (acceptor_step procs (states proc) (Receive sender msg))\<close>
      by (metis eq_snd_iff)
    thus ?thesis
    proof (cases \<open>states 0\<close>)
      case Nothing
      then show ?thesis using knowsent
      by (smt (verit, del_insts) True Un_def assms(1) assms(2) assms(3) image_iff inv3_def inv7_def invariants mem_Collect_eq prod.inject)
    next
      case (Value val)
      then show ?thesis using knowsent
      by (smt (verit, del_insts) True Un_def assms(1) assms(2) assms(3) image_iff inv3_def inv7_def invariants mem_Collect_eq prod.inject)
    next
      case (Vote_Count x3)
      then show ?thesis using knowsent
      by (smt (verit, del_insts) True Un_def assms(1) assms(2) assms(3) image_iff inv3_def inv7_def invariants mem_Collect_eq prod.inject)
    qed
  next
    case False
    hence \<open>sent = snd (proposer_step procs (states proc) event)\<close>
      using assms(4) by auto
    hence \<open>sent = snd (proposer_step procs (states proc) (Receive sender msg))\<close>
      using Receive by simp (* simp works here in an almost identical situation as above *)
    hence \<open>sent={}\<close>
      by (metis (no_types, lifting) False Receive assms(4) consensus_step.simps msg.exhaust prod.inject proposer_step.simps(2) proposer_step.simps(5) proposer_step.simps(6) proposer_step.simps(7) state.exhaust)
    then show ?thesis
      using assms(1) assms(2) by auto
  qed
next
  case (Request val)
  show ?thesis
  proof (cases \<open>proc=0\<close>)
    case True
    hence \<open>sent={}\<close> using Request assms(4) by force
    then show ?thesis
      using assms(1) assms(2) by auto
  next
    case False
    thus ?thesis
    proof(cases \<open>states proc\<close>)
      case Nothing
      hence \<open>sent={Send 0 (Propose val)}\<close>
        using Request False assms(4) by auto
      then show ?thesis
        by (smt (verit, best) UnE assms(1) assms(2) imageE inv7_def old.prod.inject send.inject singletonD)
    next
      case (Value v)
      hence \<open>sent={}\<close>
        using False assms(4) by auto
      hence \<open>msgs'=msgs\<close> by (simp add: assms(2))
      then show ?thesis by (simp add: assms(1))
    next
      case (Vote_Count f)
      hence \<open>sent={}\<close>
        using False assms(4) by auto
      hence \<open>msgs'=msgs\<close> by (simp add: assms(2))
      then show ?thesis by (simp add: assms(1))
    qed
  qed
next
  case Timeout
  hence \<open>sent={}\<close>
    by (metis acceptor_step.simps(4) assms(4) consensus_step.simps prod.inject proposer_step.simps(8))
  then show ?thesis
    using assms(1) assms(2) by auto
qed

lemma invs7:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
  shows \<open>inv7 msgs\<close>
  using assms (* USING ASSMS IS IMPORTANT HERE! *)
proof(induction events arbitrary: msgs states rule: List.rev_induct)
  case Nil
  hence \<open>msgs={}\<close> using execute_init by blast
  thus \<open>inv7 msgs\<close>
    using inv7initial by blast
next
  case (snoc x events)
  obtain proc event where \<open>x = (proc, event)\<close>
    by fastforce
  hence exec: \<open>execute consensus_step (\<lambda>p. Nothing) procs
               (events @ [(proc, event)]) msgs states\<close>
    using snoc.prems by blast
  from this obtain msgs' states' sent new_state
    where step_rel1: \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs' states'\<close>
      and step_rel2: \<open>consensus_step procs proc (states' proc) event = (new_state, sent)\<close>
      and step_rel3: \<open>msgs = msgs' \<union> ((\<lambda>msg. (proc, msg)) ` sent)\<close>
      and step_rel4: \<open>states = states' (proc := new_state)\<close>
    by auto
  have inv_before: \<open>inv7 msgs'\<close>
    using snoc.IH step_rel1 by fastforce
  then show \<open>inv7 msgs\<close>
    by (metis \<open>x=(proc,event)\<close> exec anotherinv7 inv_before step_rel4 step_rel2 step_rel3)
qed

lemma find_vote_request:\<open>find_vote (events @ [(proc, (Request val))]) = find_vote events\<close>
proof (induct events)
  case Nil
  then show ?case by auto
next
  case (Cons a events)
  then show ?case
    using find_vote_lemma2 by (metis append_Cons)
qed

lemma find_vote_timeout:\<open>find_vote (events @ [(proc, Timeout)]) = find_vote events\<close>
proof (induct events)
  case Nil
  then show ?case by auto
next
  case (Cons a events)
  then show ?case
    using find_vote_lemma2 by (metis append_Cons)
qed

lemma find_vote_accept:\<open>find_vote (events @ [(proc, Receive sender (Accept val))]) = find_vote events\<close>
proof (induct events)
  case Nil
  then show ?case by auto
next
  case (Cons a events)
  then show ?case
    using find_vote_lemma2 by (metis append_Cons)
qed

lemma find_vote_none_elim:
  assumes \<open>find_vote (a # events) p = None\<close>
  shows \<open>find_vote events p = None\<close>
proof (rule ccontr)
  assume as:\<open>find_vote events p \<noteq> None\<close>
  then obtain v where \<open>find_vote events p = Some v\<close>
    by auto
  hence \<open>find_vote (a # events) p \<noteq> None\<close>
  proof(cases \<open>is_received_vote p a\<close>)
    case True
    hence \<open>find_vote (a # events) p = Some (prop_val (recv_msg (snd a)))\<close>
      using find_vote.simps by auto
    then show ?thesis by auto
  next
    case False
    hence \<open>find_vote (a # events) p = find_vote events p\<close>
      using find_vote.simps by auto
    then show ?thesis using as by auto
  qed
  thus \<open>False\<close> using \<open>find_vote (a # events) p = None\<close> by auto
qed

lemma find_vote_nonsender:
  assumes \<open>p\<noteq>sender\<close>
  shows \<open>find_vote (events @ [(proc, Receive sender (Propose val))]) p = find_vote events p\<close>
proof (cases \<open>find_vote events p\<close>)
  case None
  have key:\<open>\<not>(is_received_vote p (proc, (Receive sender (Propose val))))\<close>
    using assms by auto
  show ?thesis using None
  proof(induct events)
    case Nil
    hence \<open>find_vote ([] @ [(proc, Receive sender (Propose val))]) p = None\<close>
      using key find_vote.simps by auto
    then show ?case by auto
  next
    case (Cons a events)
    hence \<open>find_vote events p = None\<close>
      using find_vote_none_elim by metis
    thus ?case by (metis Cons.hyps append_Cons find_vote_lemma)
  qed
next
  case (Some v)
  have key:\<open>\<not>(is_received_vote p (proc, (Receive sender (Propose val))))\<close>
    using assms by auto
  then show ?thesis
    by (simp add: Some find_vote_lemma1)
qed

lemma only_0_receives_votes:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs (events @ [(proc,event)]) msgs' states'\<close>
    and \<open>event = Receive sender (Propose val)\<close>
  shows \<open>proc=0\<close>
proof -
  have \<open>valid_event event proc msgs'\<close>
    using assms by auto
  hence \<open>((sender, Send proc (Propose val)) \<in> msgs')\<close> by (simp add: assms(2))
  moreover have \<open>inv7 msgs'\<close> 
    by (metis assms(1) invs7)
  thus ?thesis using inv7_def
  using calculation by fastforce
qed

lemma find_vote_nonzero:
  assumes \<open>proc\<noteq>0\<close>
    and \<open>execute consensus_step (\<lambda>x. Nothing) procs (events @ [(proc,event)]) msgs' states'\<close>
  shows \<open>find_vote (events @ [(proc, event)]) = find_vote events\<close>
proof -
  have \<open>\<And>sender val.(event\<noteq> Receive sender (Propose val))\<close> using assms only_0_receives_votes by metis
  hence \<open>event = Timeout \<or> (\<exists> val.(event = Request val)) \<or> (\<exists> sender val.(event = Receive sender (Accept val)))\<close>
    by (metis event.exhaust msg.exhaust)
  thus ?thesis using find_vote_timeout find_vote_request find_vote_accept by metis
qed

lemma only0lemma:
  assumes \<open>states 0 = states' 0\<close>
    and \<open>inv4 procs events states \<and> inv5 procs events states \<and> inv6 procs events states\<close>
  shows \<open>inv4 procs events states' \<and> inv5 procs events states' \<and> inv6 procs events states'\<close>
proof(cases \<open>procs\<subseteq>{0}\<close>)
  case True
  then show ?thesis by (metis assms(1) assms(2) inv4_def inv5_def inv6_def)
next
  case False
  hence \<open>\<forall>val. states 0 = Value val \<longrightarrow> Some val \<in> set_of_potential_winners procs (find_vote events)\<close>
    using assms(2) by (metis inv4_def)
  then show ?thesis by (metis assms(1) assms(2) inv4_def inv5_def inv6_def)
qed

lemma find_vote_already_done:
  fixes pp
  assumes \<open>states 0 = Value v\<close>
    and \<open>inv4 procs events states \<and> inv5 procs events states\<close>
    and \<open>pp\<noteq>0\<close>
    and \<open>pp\<in> procs\<close>
  shows \<open>find_vote (events @ [(p, event)]) pp = find_vote events pp\<close>
proof -
  have \<open>\<not>(not_every_vote_counted procs (find_vote events))\<close>
    using assms(1) assms(2) inv5_def by metis
  hence h:\<open>\<forall>proc\<in>procs.(((find_vote events) proc \<noteq> None) \<or> proc=0)\<close> by auto
  hence \<open>(find_vote events) pp \<noteq> None\<close> using assms(4) assms(3) by auto
  then obtain val where \<open>(find_vote events) pp = Some val\<close> by auto
  then show ?thesis
    using find_vote_lemma1 by metis
qed

lemma potential_winners_request:\<open>set_of_potential_winners procs (find_vote (events @ [(proc, (Request val))])) = set_of_potential_winners procs (find_vote events)\<close>
  using find_vote_request by metis

lemma potential_winners_timeout:\<open>set_of_potential_winners procs (find_vote (events @ [(proc, Timeout)])) = set_of_potential_winners procs (find_vote events)\<close>
  using find_vote_timeout by metis

lemma anotherinv8:
  assumes \<open>inv8 events states\<close>
    and \<open>msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)\<close>
    and \<open>execute consensus_step (\<lambda>x. Nothing) procs (events @ [(proc,event)]) msgs' states'\<close>
    and \<open>consensus_step procs proc (states proc) event = (new_state, sent)\<close>
    and \<open>states' = states(proc:=new_state)\<close>
  shows \<open>inv8 (events @ [(proc,event)]) states'\<close>
proof(cases event)
  case (Receive sender msg)
  then show ?thesis
  proof(cases \<open>states 0\<close>)
    case Nothing
    hence kk:\<open>find_vote events = initial_vote_count\<close>
      using inv8_def assms(1) by auto
    then show ?thesis
    proof (cases \<open>proc=0\<close>)
      case True
      then show ?thesis
      proof (cases msg)
        case (Propose val)
        hence k:\<open>new_state = fst (count_update procs initial_vote_count sender val)\<close>
          using assms(4) by (simp add: Receive True Nothing)
        hence \<open>new_state \<noteq> Nothing\<close>
        proof(cases \<open>not_every_vote_counted procs (initial_vote_count (sender := Some val))\<close>)
          case True
          hence \<open>count_update procs initial_vote_count sender val = (Vote_Count (initial_vote_count(sender:= Some val)), {})\<close>
            using count_update.simps by auto
          hence \<open>new_state = Vote_Count (initial_vote_count(sender:= Some val))\<close> by (simp add: k)
          then show ?thesis by auto
        next
          let ?w=\<open>(the (pick_winner (procs\<union>{sender}) (initial_vote_count (sender := Some val))))\<close>
          have non:\<open>initial_vote_count sender = None\<close> by auto
          case False
          hence \<open>count_update procs initial_vote_count sender val
                              = (set_value_and_send_accept_all (procs\<union>{sender}) ?w)\<close>
              using non count_update.simps by (smt (verit, best) option.simps(4))
          hence \<open>fst (count_update procs initial_vote_count sender val) = Value ?w\<close>
            by simp
          hence \<open>new_state = Value ?w\<close> by (simp add: k)
          then show ?thesis by auto
        qed
        then show ?thesis
          by (simp add: True assms(5) inv8_def)
      next
        case (Accept val)
        hence \<open>find_vote events = find_vote (events @ [(proc,event)])\<close>
          using find_vote_accept by (metis Receive)
        hence \<open>find_vote (events @ [(proc,event)]) = initial_vote_count\<close>
          by (simp add: kk)
        then show ?thesis
          using inv8_def by auto
      qed
    next
      case False
      hence \<open>find_vote events = find_vote (events @ [(proc,event)])\<close>
        using find_vote_nonzero by (metis assms(3))
      hence \<open>find_vote (events @ [(proc,event)]) = initial_vote_count\<close>
        by (simp add: kk)
      then show ?thesis
        using inv8_def by auto
    qed
  next
    case (Value val)
    then show ?thesis
    proof (cases \<open>proc=0\<close>)
      case True
      then show ?thesis
      proof (cases msg)
        case (Propose v)
        then show ?thesis
          using Receive True Value assms(4) assms(5) inv8_def by fastforce
      next
        case (Accept w)
        then show ?thesis
          using Receive True Value assms(4) assms(5) inv8_def by fastforce
      qed
    next
      case False
      then show ?thesis
        by (simp add: Value assms(5) inv8_def)
    qed
  next
    case (Vote_Count f)
    then show ?thesis
    proof (cases \<open>proc=0\<close>)
      case True
      then show ?thesis
      proof (cases msg)
        case (Propose val)
        hence k:\<open>new_state = fst (count_update procs f sender val)\<close>
          using assms(4) by (simp add: Receive True Vote_Count)
        hence \<open>new_state \<noteq> Nothing\<close> using Receive True Vote_Count assms(4)
        proof (cases \<open>f sender\<close>)
          case None
          then show ?thesis
          proof(cases \<open>not_every_vote_counted procs (f (sender := Some val))\<close>)
            case True
            hence \<open>count_update procs f sender val = (Vote_Count (f(sender:= Some val)), {})\<close>
              using None count_update.simps by auto
            hence \<open>new_state = Vote_Count (f(sender:= Some val))\<close> by (simp add: k)
            then show ?thesis by auto
          next
            let ?w=\<open>(the (pick_winner (procs\<union>{sender}) (f (sender := Some val))))\<close>
            case False
            hence \<open>count_update procs f sender val
                                = (set_value_and_send_accept_all (procs\<union>{sender}) ?w)\<close>
              using None count_update.simps by (smt (verit, best) option.simps(4))
            hence \<open>fst (count_update procs f sender val) = Value ?w\<close>
              by simp
            hence \<open>new_state = Value ?w\<close> by (simp add: k)
            then show ?thesis by auto
          qed
        next
          case (Some w)
          hence \<open>count_update procs f sender val = (Vote_Count f, {})\<close>
            using count_update.simps by auto
          hence \<open>new_state = Vote_Count f\<close> by (simp add: k)
          then show ?thesis by auto
        qed
        then show ?thesis
          by (simp add: True assms(5) inv8_def)
      next
        case (Accept w)
        then show ?thesis
          using Receive True Vote_Count assms(4) assms(5) inv8_def by fastforce
      qed
    next
      case False
      then show ?thesis
        by (simp add: Vote_Count assms(5) inv8_def)
    qed
  qed
next
  case (Request val)
  then show ?thesis
  proof(cases \<open>states 0\<close>)
    case Nothing
    hence \<open>find_vote events=initial_vote_count\<close> using assms(1) inv8_def by blast
    hence \<open>find_vote (events @ [(proc,event)]) = initial_vote_count\<close>
      using find_vote_request by (metis Request)
    then show ?thesis using inv8_def by blast
  next
    case (Value val)
    hence \<open>states' 0 \<noteq> Nothing\<close>
      using Request acceptor_step.simps(4) assms(4) assms(5) consensus_step.simps fun_upd_apply by auto
    then show ?thesis using inv8_def by blast
  next
    case (Vote_Count x3)
    hence \<open>states' 0 \<noteq> Nothing\<close>
      using Request acceptor_step.simps(4) assms(4) assms(5) consensus_step.simps fun_upd_apply by auto
    then show ?thesis using inv8_def by blast
  qed
next
  case Timeout
  then show ?thesis
  proof(cases \<open>states 0\<close>)
    case Nothing
    hence \<open>find_vote events=initial_vote_count\<close> using assms(1) inv8_def by blast
    hence \<open>find_vote (events @ [(proc,event)]) = initial_vote_count\<close>
      using find_vote_timeout by (metis Timeout)
    then show ?thesis using inv8_def by blast
  next
    case (Value val)
    hence \<open>states' 0 \<noteq> Nothing\<close>
      using Timeout acceptor_step.simps(4) assms(4) assms(5) consensus_step.simps fun_upd_apply by auto
    then show ?thesis using inv8_def by blast
  next
    case (Vote_Count x3)
    hence \<open>states' 0 \<noteq> Nothing\<close>
      using Timeout acceptor_step.simps(4) assms(4) assms(5) consensus_step.simps fun_upd_apply by auto
    then show ?thesis using inv8_def by blast
  qed
qed

lemma invs8:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
  shows \<open>inv8 events states\<close>
  using assms (* USING ASSMS IS IMPORTANT HERE! *)
proof(induction events arbitrary: msgs states rule: List.rev_induct)
  case Nil
  thus \<open>inv8 [] states\<close>
    using inv8initial by blast
next
  case (snoc x events)
  obtain proc event where \<open>x = (proc, event)\<close>
    by fastforce
  hence exec: \<open>execute consensus_step (\<lambda>p. Nothing) procs
               (events @ [(proc, event)]) msgs states\<close>
    using snoc.prems by blast
  from this obtain msgs' states' sent new_state
    where step_rel1: \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs' states'\<close>
      and step_rel2: \<open>consensus_step procs proc (states' proc) event = (new_state, sent)\<close>
      and step_rel3: \<open>msgs = msgs' \<union> ((\<lambda>msg. (proc, msg)) ` sent)\<close>
      and step_rel4: \<open>states = states' (proc := new_state)\<close>
    by auto
  have inv_before: \<open>inv8 events states'\<close>
    using snoc.IH step_rel1 by fastforce
  then show \<open>inv8 (events @ [x]) states\<close>
    by (metis \<open>x=(proc,event)\<close> exec anotherinv8 inv_before step_rel4 step_rel2 step_rel3)
qed

lemma inv4_request:
  assumes \<open>inv4 procs events states\<close>
  shows \<open>inv4 procs (events @ [(proc, (Request val))]) states\<close>
proof (cases \<open>procs \<subseteq> {0}\<close>)
  case True
  then show ?thesis using inv4_def by auto
next
  case False
  then show ?thesis
  proof (cases \<open>states 0\<close>)
    case Nothing
    hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
    then show ?thesis using inv4_def by blast
  next
    case (Value w)
    have \<open>\<And>v.(states 0 = Value v \<Longrightarrow>
                   (Some v \<in> set_of_potential_winners procs (find_vote (events @ [(proc, (Request val))]))))\<close>
    proof -
      fix v
      assume a:\<open>states 0 = Value v\<close>
      thus \<open>Some v \<in> set_of_potential_winners procs (find_vote (events @ [(proc, (Request val))]))\<close>
      proof (cases \<open>v=w\<close>)
        case True
        then show ?thesis using potential_winners_request
        by (metis False a assms inv4_def)
      next
        case False
        then show ?thesis
        by (metis Value a state.inject(1))
      qed
    qed
    hence \<open>\<forall>v.(states 0 = Value v \<longrightarrow>
                   (Some v \<in> set_of_potential_winners procs (find_vote (events @ [(proc, (Request val))]))))\<close>
      by auto
    then show ?thesis by (simp add: inv4_def)
  next
    case (Vote_Count f)
    hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
    then show ?thesis using inv4_def by blast
  qed
qed

lemma inv4_timeout:
  assumes \<open>inv4 procs events states\<close>
  shows \<open>inv4 procs (events @ [(proc, Timeout)]) states\<close>
proof (cases \<open>procs \<subseteq> {0}\<close>)
  case True
  then show ?thesis using inv4_def by auto
next
  case False
  then show ?thesis
  proof (cases \<open>states 0\<close>)
    case Nothing
    hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
    then show ?thesis using inv4_def by blast
  next
    case (Value w)
    have \<open>\<And>v.(states 0 = Value v \<Longrightarrow>
                   (Some v \<in> set_of_potential_winners procs (find_vote (events @ [(proc, Timeout)]))))\<close>
    proof -
      fix v
      assume a:\<open>states 0 = Value v\<close>
      thus \<open>Some v \<in> set_of_potential_winners procs (find_vote (events @ [(proc, Timeout)]))\<close>
      proof (cases \<open>v=w\<close>)
        case True
        then show ?thesis using potential_winners_timeout
        by (metis False a assms inv4_def)
      next
        case False
        then show ?thesis
        by (metis Value a state.inject(1))
      qed
    qed
    hence \<open>\<forall>v.(states 0 = Value v \<longrightarrow>
                   (Some v \<in> set_of_potential_winners procs (find_vote (events @ [(proc, Timeout)]))))\<close>
      by auto
    then show ?thesis by (simp add: inv4_def)
  next
    case (Vote_Count f)
    hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
    then show ?thesis using inv4_def by blast
  qed
qed

lemma inv5_request:
  assumes \<open>inv5 procs events states\<close>
  shows \<open>inv5 procs (events @ [(proc, (Request val))]) states\<close>
proof (cases \<open>states 0\<close>)
  case Nothing
  hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
  then show ?thesis using inv5_def by blast
next
  case (Value w)
  have \<open>\<And>v.(states 0 = Value v \<Longrightarrow>
                 (\<not>(not_every_vote_counted procs (find_vote (events @ [(proc, (Request val))])))))\<close>
    by (metis assms find_vote_request inv5_def)
  hence \<open>\<forall>v.(states 0 = Value v \<longrightarrow>
                 (\<not>(not_every_vote_counted procs (find_vote (events @ [(proc, (Request val))])))))\<close>
    by auto
  then show ?thesis by (simp add: inv5_def)
next
  case (Vote_Count f)
  hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
  then show ?thesis using inv5_def by blast
qed

lemma inv5_timeout:
  assumes \<open>inv5 procs events states\<close>
  shows \<open>inv5 procs (events @ [(proc, Timeout)]) states\<close>
proof (cases \<open>states 0\<close>)
  case Nothing
  hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
  then show ?thesis using inv5_def by blast
next
  case (Value w)
  have \<open>\<And>v.(states 0 = Value v \<Longrightarrow>
                 (\<not>(not_every_vote_counted procs (find_vote (events @ [(proc, Timeout)])))))\<close>
    by (metis assms find_vote_timeout inv5_def)
  hence \<open>\<forall>v.(states 0 = Value v \<longrightarrow>
                 (\<not>(not_every_vote_counted procs (find_vote (events @ [(proc, Timeout)])))))\<close>
    by auto
  then show ?thesis by (simp add: inv5_def)
next
  case (Vote_Count f)
  hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
  then show ?thesis using inv5_def by blast
qed

lemma inv6_request:
  assumes \<open>inv6 procs events states\<close>
  shows \<open>inv6 procs (events @ [(proc, (Request val))]) states\<close>
proof (cases \<open>states 0\<close>)
  case Nothing
  hence \<open>\<forall>f. states 0 \<noteq> Vote_Count f\<close> by auto
  then show ?thesis using inv6_def by blast
next
  case (Value w)
  hence \<open>\<forall>f. states 0 \<noteq> Vote_Count f\<close> by auto
  then show ?thesis using inv6_def by blast
next
  case (Vote_Count f)
  have \<open>find_vote events = find_vote (events @ [(proc, (Request val))])\<close>
    by (simp add: find_vote_request)
  moreover have \<open>not_every_vote_counted procs (find_vote events)\<close>
    using Vote_Count assms inv6_def by blast
  ultimately show ?thesis 
    by (metis (no_types, lifting) assms inv6_def)
qed

lemma inv6_timeout:
  assumes \<open>inv6 procs events states\<close>
  shows \<open>inv6 procs (events @ [(proc, Timeout)]) states\<close>
proof (cases \<open>states 0\<close>)
  case Nothing
  hence \<open>\<forall>f. states 0 \<noteq> Vote_Count f\<close> by auto
  then show ?thesis using inv6_def by blast
next
  case (Value w)
  hence \<open>\<forall>f. states 0 \<noteq> Vote_Count f\<close> by auto
  then show ?thesis using inv6_def by blast
next
  case (Vote_Count f)
  have \<open>find_vote events = find_vote (events @ [(proc, Timeout)])\<close>
    by (simp add: find_vote_timeout)
  moreover have \<open>not_every_vote_counted procs (find_vote events)\<close>
    using Vote_Count assms inv6_def by blast
  ultimately show ?thesis 
    by (metis (no_types, lifting) assms inv6_def)
qed

lemma some_lemma: \<open>Some (the (Some v)) = Some v\<close>
  by auto

lemma anotherinv456pnonzero:
  assumes \<open>p\<noteq>0\<close>
    and \<open>inv4 procs events states \<and> inv5 procs events states \<and> inv6 procs events states\<close>
    and \<open>states' 0 = states 0\<close>
    and \<open>execute consensus_step (\<lambda>x. Nothing) procs (events @ [(p,event)]) msgs' states'\<close>
  shows \<open>inv4 procs (events @ [(p,event)]) states' \<and> inv5 procs (events @ [(p,event)]) states'
          \<and> inv6 procs (events @ [(p,event)]) states'\<close>
proof (cases \<open>states 0\<close>)
  case Nothing
  hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
  moreover have \<open>\<forall>f. states 0 \<noteq> Vote_Count f\<close> using Nothing by auto
  ultimately show ?thesis using inv4_def inv5_def inv6_def
    by (metis assms(3))
next
  case (Value w)
  hence key:\<open>\<And>pp. (pp\<in>procs\<and>pp\<noteq>0 \<Longrightarrow>find_vote (events @ [(p, event)]) pp = find_vote events pp)\<close>
    using find_vote_already_done by (metis assms(2))
  hence key2:\<open>\<And>pp val.((pp\<in>procs) \<Longrightarrow> ((find_vote (events @ [(p,event)])) pp = val \<and> pp\<noteq>0) \<longleftrightarrow> ((find_vote events) pp = val) \<and> pp\<noteq>0)\<close>
    by auto
  hence \<open>\<And> val. (\<exists>pp\<in>procs. (find_vote (events @ [(p,event)])) pp = val \<and> pp \<noteq> 0) \<longleftrightarrow> (\<exists>pp\<in>procs. (find_vote events) pp = val \<and> pp \<noteq> 0)\<close>
    by auto
  hence \<open>{val.(\<exists>pp\<in>procs. (find_vote (events @ [(p,event)])) pp = val \<and> pp \<noteq> 0)} = {val.(\<exists>pp\<in>procs. (find_vote events) pp = val \<and> pp \<noteq> 0)}\<close>
    by auto
  hence hvals:\<open>vals_with_votes procs (find_vote (events @ [(p, event)])) = vals_with_votes procs (find_vote events)\<close>
    by auto
  have \<open>\<And>val.({pp\<in> procs . (find_vote (events @ [(p, event)])) pp = val \<and> pp\<noteq>0}={pp\<in> procs . (find_vote events) pp = val \<and> pp\<noteq>0})\<close>
    using key2 by auto
  hence hh:\<open>nonzero_counter procs (find_vote (events @ [(p, event)])) = nonzero_counter procs (find_vote events)\<close>
    by auto
  hence \<open>most_vote_counts procs (find_vote (events @ [(p, event)])) = most_vote_counts procs (find_vote events)\<close>
    using hvals by auto
  hence \<open>set_of_potential_winners procs (find_vote (events @ [(p, event)]))
          = set_of_potential_winners procs (find_vote events)\<close>
    using hh by auto
  moreover have \<open>states' 0 = states 0\<close> using assms(3) assms(1) by auto
  hence \<open>inv4 procs events states' \<and> inv5 procs events states' \<and> inv6 procs events states'\<close>
    using only0lemma by (metis assms(2))
  ultimately have ult1:\<open>inv4 procs (events @ [(p,event)]) states'\<close>
    using inv4_def by blast
  have \<open>\<not>(not_every_vote_counted procs (find_vote events))\<close>
    by (meson Value assms(2) inv5_def)
  hence \<open>\<not>(not_every_vote_counted procs (find_vote (events @ [(p, event)])))\<close>
    using key by auto
  hence ult2:\<open>inv5 procs (events @ [(p,event)]) states'\<close> using inv5_def by auto
  have \<open>\<forall>f. states 0 \<noteq> Vote_Count f\<close> using Value by auto
  thus ?thesis using ult1 ult2
    by (simp add: assms(3) inv6_def)
next
  case (Vote_Count f)
  hence \<open>\<forall>v. states 0 \<noteq> Value v\<close> by auto
  hence h:\<open>inv4 procs (events @ [(p,event)]) states' \<and> inv5 procs (events @ [(p,event)]) states'\<close>
    using inv4_def inv5_def by (metis assms(3))
  have \<open>inv4 procs events states' \<and> inv5 procs events states' \<and> inv6 procs events states'\<close>
    using only0lemma assms(2) by (metis assms(3))
  moreover have \<open>find_vote events = find_vote (events @ [(p,event)])\<close>
    using find_vote_nonzero assms(1) assms(4) by metis
  moreover have \<open>not_every_vote_counted procs (find_vote events)\<close>
    using Vote_Count assms inv6_def by blast
  ultimately have \<open>inv6 procs (events @ [(p,event)]) states'\<close>
    using inv6_def by metis
  thus ?thesis using h by auto
qed

lemma state_value_does_not_change:
  assumes \<open>consensus_step procs 0 (Value w) event = (new_state, sent)\<close>
  shows \<open>new_state = Value w\<close>
proof (cases \<open>\<exists>sender val. (event = (Receive sender (Propose val)))\<close>)
  have \<open>consensus_step procs 0 (Value w) event = acceptor_step procs (Value w) event\<close> by auto
  hence h:\<open>new_state = fst (acceptor_step procs (Value w) event)\<close>
    using assms by auto
  case True
  obtain sender where \<open>acceptor_step procs (Value w) event = (Value w, {Send sender (Accept w)})\<close>
    using True by auto
  thus \<open>new_state = Value w\<close> using h by auto
next
  case False
  hence \<open>acceptor_step procs (Value w) event = (Value w, {})\<close>
    by (metis acceptor_step.simps(2) acceptor_step.simps(3) acceptor_step.simps(4) event.exhaust msg.exhaust)
  then show ?thesis 
    using assms by auto
qed

lemma anotherinv456pzero:
  assumes \<open>consensus_step procs 0 (states 0) event = (new_state, sent)\<close>
    and \<open>states' = states(0:=new_state)\<close>
    and \<open>inv4 procs events states \<and> inv5 procs events states \<and> inv6 procs events states\<close>
    and \<open>execute consensus_step (\<lambda>x. Nothing) procs (events @ [(0,event)]) msgs' states'\<close>
    and \<open>msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)\<close>
    and \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
    and \<open>finite procs\<close>
  shows \<open>inv4 procs (events @ [(0,event)]) states' \<and> inv5 procs (events @ [(0,event)]) states'
          \<and> inv6 procs (events @ [(0,event)]) states'\<close>
proof(cases event)
  case (Receive sender msg)
  then show ?thesis
  proof(cases msg)
    case (Propose v)
    thus ?thesis
    proof (cases \<open>states' 0\<close>)
      case Nothing
      then show ?thesis
        by (simp add: inv4_def inv5_def inv6_def)
    next
      case (Value val)
      thus ?thesis
      proof(cases \<open>states 0\<close>)
        case Nothing
        hence \<open>new_state= Value val\<close>
          using Value assms(2) by auto
        hence h:\<open>(Value val,sent) = (count_update procs initial_vote_count sender v)\<close>
          using assms(1) by (simp add: Propose Receive Nothing)
        have knowfind:\<open>find_vote events = initial_vote_count\<close>
          using Nothing invs8 assms(6) inv8_def by blast
        moreover have hh:\<open>initial_vote_count sender = None\<close> by auto
        moreover have hy:\<open>\<not>(not_every_vote_counted procs (initial_vote_count (sender := Some v)))\<close>
        proof(rule ccontr)
          assume \<open>\<not> \<not> not_every_vote_counted procs (initial_vote_count(sender \<mapsto> v))\<close>
          hence \<open>not_every_vote_counted procs (initial_vote_count(sender \<mapsto> v))\<close> by auto
          hence \<open>(Vote_Count (initial_vote_count(sender \<mapsto> v)), {}) = (count_update procs initial_vote_count sender v)\<close>
            using hh count_update.simps by auto
          hence \<open>Value val = Vote_Count (initial_vote_count(sender \<mapsto> v))\<close> using h by auto
          thus False by auto
        qed
        (*hence \<open>Value val = fst(set_value_and_send_accept_all (procs\<union>{sender}) (the (pick_winner (procs\<union>{sender}) (initial_vote_count (sender := Some v)))))\<close>
          using h hh count_update.simps *)
        have \<open>event = Receive sender (Propose v)\<close>
          by (simp add: Propose Receive)
        hence thiscase:\<open>(consensus_step procs 0 (states 0) event) = (acceptor_step procs Nothing (Receive sender (Propose v)))\<close>
          using Nothing by simp
        hence ha:\<open>sent =snd (acceptor_step procs Nothing (Receive sender (Propose v)))\<close>
          using assms(1) by (smt (verit, best) sndI)
        have h:\<open>acceptor_step procs Nothing (Receive sender (Propose v))
                       = count_update procs initial_vote_count sender v\<close> by simp
        let ?w=\<open>(the (pick_winner (procs\<union>{sender}) (initial_vote_count (sender := Some v))))\<close>
        have hz:\<open>count_update procs initial_vote_count sender v = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close>
          apply (simp only: count_update.simps hh hy)
          by simp
        have hw:\<open>set_value_and_send_accept_all (procs\<union>{sender}) ?w = (Value ?w,((\<lambda>p. (Send p (Accept ?w))) ` (procs\<union>{sender})))\<close>
          by simp
        hence sentis:\<open>sent = ((\<lambda>p. (Send p (Accept ?w))) ` (procs\<union>{sender}))\<close> using ha h hz hw by simp
        hence \<open>\<forall>x\<in>sent. send_msg x = (Accept ?w)\<close>
          by force
        moreover have \<open>send_msg (Send 0 (Propose v))\<noteq> (Accept ?w)\<close>
          by (metis msg.distinct(1) send.sel(2))
        ultimately have \<open>Send 0 (Propose v) \<notin> sent\<close> by auto
        hence \<open>(sender, Send 0 (Propose v))\<in> msgs\<close>
          using \<open>event = Receive sender (Propose v)\<close> assms(4) assms(5) image_iff by auto
        hence nonzero:\<open>sender\<noteq>0\<close>
          by (metis \<open>event = Receive sender (Propose v)\<close> assms(4) execute_receive inv3_def invariants)
        have theprocs:\<open>\<forall>p\<in>procs. p=0\<or>p=sender\<close>
        using hy by fastforce
        hence theprocscont:\<open>(procs\<union>{sender})\<subseteq>{0,sender}\<close> by blast
        hence pexist:\<open>\<exists>p\<in>(procs\<union>{sender}). (((initial_vote_count(sender:= Some v)) p) = (Some v) \<and> p \<noteq> 0)\<close>
          using nonzero by auto
        hence \<open>Some v \<in> {u.\<exists>p\<in>(procs\<union>{sender}). (((initial_vote_count(sender:= Some v)) p) = u \<and> p \<noteq> 0)}\<close>
          by simp
        hence valin:\<open>Some v \<in> vals_with_votes (procs\<union>{sender}) (initial_vote_count(sender:= Some v))\<close>
          by auto
        have knowvotes:\<open>find_vote (events @ [(0,event)]) = initial_vote_count(sender:= Some v)\<close>
        proof
          fix p
          show \<open>find_vote (events @ [(0, event)]) p = (initial_vote_count(sender \<mapsto> v)) p\<close>
          proof(cases \<open>p=sender\<close>)
            case True
            have \<open>find_vote events sender = None\<close>
              using knowfind by simp
            hence \<open>find_vote (events @ [(0, Receive sender (Propose v))]) sender = Some v\<close>
            proof(induct events)
              case Nil
              then show ?case by auto
            next
              case (Cons a events)
              hence \<open>find_vote events sender = None\<close>
                using find_vote_none_elim by metis
              moreover have \<open>\<not>is_received_vote sender a\<close>
                using \<open>find_vote (a # events) sender = None\<close> find_vote.simps by auto
              hence \<open>find_vote (events @ [(0, Receive sender (Propose v))]) sender
                     = find_vote ((a# events) @ [(0, Receive sender (Propose v))]) sender\<close>
                by auto
              ultimately show ?case
                using \<open>find_vote events sender = None \<Longrightarrow> find_vote (events @ [(0, Receive sender (Propose v))]) sender = Some v\<close>
                by auto
            qed
            hence \<open>find_vote (events @ [(0, event)]) sender = Some v\<close> using Receive Propose by auto
            then show ?thesis 
              by (simp add: True)
          next
            case False
            hence \<open>(initial_vote_count(sender \<mapsto> v)) p = None\<close>
              using nonzero by simp
            moreover have \<open>find_vote (events @ [(0, event)]) p = find_vote events p\<close>
              using find_vote_nonsender by (metis False \<open>event = Receive sender (Propose v)\<close>)
            ultimately show ?thesis
              using knowfind by auto
          qed
        qed
        moreover have \<open>\<exists>p\<in>(procs\<union>{sender}). (((initial_vote_count(sender:= Some v)) p) = u \<and> p \<noteq> 0)\<longrightarrow>u=Some v\<close>
          by simp
        hence \<open>{u.\<exists>p\<in>(procs\<union>{sender}). (((initial_vote_count(sender:= Some v)) p) = u \<and> p \<noteq> 0)}\<subseteq> {Some v}\<close>
          using theprocs by auto
        hence knowvalswithvotes:\<open>vals_with_votes (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) = {Some v}\<close>
          by (smt (z3) Collect_cong \<open>Some v \<in> {u. \<exists>p\<in>procs \<union> {sender}. (initial_vote_count(sender \<mapsto> v)) p = u \<and> p \<noteq> 0}\<close> empty_iff subset_singleton_iff vals_with_votes.elims)
        hence \<open>sender\<in>{p\<in> (procs\<union>{sender}) . ((initial_vote_count(sender:= Some v)) p = (Some v) \<and> p\<noteq>0)}\<close>
        using theprocs by fastforce
        hence somevalcount:\<open>nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) (Some v) =1\<close>
          using pexist by simp
        hence \<open>(nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)))`(vals_with_votes (procs\<union>{sender}) (initial_vote_count(sender:= Some v))) = {1}\<close>
          by (metis knowvalswithvotes image_insert image_is_empty)
        hence mostvotes1:\<open>most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) = 1\<close> by simp
        hence \<open>nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) (Some v) = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some v))\<close>
          using somevalcount by linarith
        hence somevalcontainment:\<open>Some v \<in> set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some v))\<close>
          by simp
        moreover have \<open>\<And>somev.(somev\<noteq> Some v \<longrightarrow> {p\<in> (procs\<union>{sender}) . ((initial_vote_count(sender:= Some v)) p = somev \<and> p\<noteq>0)} = {})\<close>
          using theprocs by fastforce
        hence \<open>\<And>somev.(somev\<noteq> Some v \<longrightarrow> card{p\<in> (procs\<union>{sender}) . ((initial_vote_count(sender:= Some v)) p = somev \<and> p\<noteq>0)} =0)\<close>
          by (metis (no_types, lifting) card.empty)
        hence \<open>\<And>somev.(somev\<noteq> Some v \<longrightarrow> nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) somev =0)\<close>
          by simp
        hence conp:\<open>\<And>somev.(somev \<noteq> Some v \<longrightarrow> nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) somev \<noteq> most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some v)))\<close>
          using mostvotes1 by simp
        hence conp2:\<open>\<And>somev.(\<not>(somev = Some v) \<Longrightarrow> \<not>(nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) somev = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some v))))\<close>
          by auto
        hence \<open>\<And>somev.((nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) somev = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some v))) \<Longrightarrow> somev=Some v)\<close>
          using flip_contrap by blast
        hence cont:\<open>\<And>somev.((nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) somev = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some v))) \<Longrightarrow> somev\<in>{Some v})\<close>
          by blast
        have \<open>set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) \<subseteq> {Some v}\<close>
        proof
          fix x
          assume as:\<open>x\<in> set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some v))\<close>
          hence \<open>x\<in>{some.(nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) some = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some v)))}\<close>
            by simp
          hence \<open>(nonzero_counter (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) x = most_vote_counts (procs\<union>{sender}) (initial_vote_count(sender:= Some v)))\<close>
            by simp
          thus \<open>x\<in>{Some v}\<close> using cont
          by blast
        qed
        hence \<open>set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) = {Some v}\<close>
          using somevalcontainment by fastforce
        hence simper:\<open>{Some v} = set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some v))\<close>
          by auto
        moreover have \<open>(SOME u. u \<in> {Some v}) = Some v\<close>
          by simp
        hence \<open>(SOME u. u \<in> set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some v))) = Some v\<close>
          using simper by simp
        hence \<open>pick_winner (procs\<union>{sender}) (initial_vote_count(sender:= Some v)) = Some v\<close>
          by simp
        hence valwins:\<open>the (pick_winner (procs\<union>{sender}) (initial_vote_count(sender:= Some v))) = v\<close>
          by auto
        hence exactsent:\<open>sent = ((\<lambda>p. (Send p (Accept v))) ` (procs\<union>{sender}))\<close>
          using sentis by simp
        hence \<open>msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` ((\<lambda>p. (Send p (Accept v))) ` (procs\<union>{sender})))\<close>
          using assms(5) by simp
        hence knowmsgs1:\<open>msgs' = msgs \<union> ((\<lambda>p. (0,(Send p (Accept v)))) ` (procs\<union>{sender}))\<close>
          by auto
        hence knowmsgs2:\<open>msgs'\<subseteq> msgs\<union> {(0, (Send sender (Accept v))),(0,(Send 0 (Accept v)))}\<close>
          using theprocscont by auto
        moreover have knowstates:\<open>states' = states (0 := Value v)\<close>
          by (metis Pair_inject thiscase valwins assms(1) assms(2) h hw hz)
        hence \<open>val=v\<close> using Value by fastforce
        hence \<open>{Some val} = set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some v))\<close>
          by (simp add: simper)
        hence \<open>Some val \<in> set_of_potential_winners (procs\<union>{sender}) (initial_vote_count(sender:= Some v))\<close>
          by blast
        hence vin2:\<open>Some val \<in> set_of_potential_winners (procs\<union>{sender}) (find_vote (events @ [(0,event)]))\<close>
          by (simp add: knowvotes)
        hence i4:\<open>inv4 procs (events @ [(0,event)]) states'\<close>
        proof (cases \<open>procs \<subseteq> {0}\<close>)
          case True
          then show ?thesis using inv4_def by auto
        next
          case False
          hence \<open>sender\<in>procs\<close> using theprocs by auto
          hence \<open>procs\<union>{sender}=procs\<close> by auto
          hence \<open>Some val \<in> set_of_potential_winners (procs) (find_vote (events @ [(0,event)]))\<close>
            using vin2 by simp
          then show ?thesis
            using inv4_def by (metis Value state.inject(1))
        qed
        have \<open>\<not>(not_every_vote_counted procs (find_vote (events @ [(0,event)])))\<close>
          using hy knowvotes by presburger
        hence i5:\<open>inv5 procs (events @ [(0,event)]) states'\<close>
          using inv5_def by auto
        have i6:\<open>inv6 procs (events @ [(0,event)]) states'\<close>
          by (simp add: Value inv6_def)
        thus ?thesis using i4 i5 i6 by auto
      next
        case (Value w)
        hence key:\<open>\<And>pp. (pp\<in>procs\<and>pp\<noteq>0 \<Longrightarrow>find_vote (events @ [(0, event)]) pp = find_vote events pp)\<close>
          using find_vote_already_done by (metis assms(3))
        hence key2:\<open>\<And>pp val.((pp\<in>procs) \<Longrightarrow> ((find_vote (events @ [(0,event)])) pp = val \<and> pp\<noteq>0) \<longleftrightarrow> ((find_vote events) pp = val) \<and> pp\<noteq>0)\<close>
          by auto
        hence \<open>\<And> val. (\<exists>pp\<in>procs. (find_vote (events @ [(0,event)])) pp = val \<and> pp \<noteq> 0) \<longleftrightarrow> (\<exists>pp\<in>procs. (find_vote events) pp = val \<and> pp \<noteq> 0)\<close>
          by auto
        hence \<open>{val.(\<exists>pp\<in>procs. (find_vote (events @ [(0,event)])) pp = val \<and> pp \<noteq> 0)} = {val.(\<exists>pp\<in>procs. (find_vote events) pp = val \<and> pp \<noteq> 0)}\<close>
          by auto
        hence hvals:\<open>vals_with_votes procs (find_vote (events @ [(0, event)])) = vals_with_votes procs (find_vote events)\<close>
          by auto
        have \<open>\<And>val.({pp\<in> procs . (find_vote (events @ [(0, event)])) pp = val \<and> pp\<noteq>0}={pp\<in> procs . (find_vote events) pp = val \<and> pp\<noteq>0})\<close>
          using key2 by auto
        hence hh:\<open>nonzero_counter procs (find_vote (events @ [(0, event)])) = nonzero_counter procs (find_vote events)\<close>
          by auto
        hence \<open>most_vote_counts procs (find_vote (events @ [(0, event)])) = most_vote_counts procs (find_vote events)\<close>
          using hvals by auto
        hence \<open>set_of_potential_winners procs (find_vote (events @ [(0, event)]))
                = set_of_potential_winners procs (find_vote events)\<close>
          using hh by auto
        moreover have \<open>states' 0 = states 0\<close>
          using \<open>states' 0 = Value val\<close> Value state_value_does_not_change assms(1) assms(2) by fastforce
        ultimately have ult1:\<open>inv4 procs (events @ [(0,event)]) states'\<close>
          using inv4_def by (metis assms(3))
        have \<open>\<not>(not_every_vote_counted procs (find_vote events))\<close>
          by (meson Value assms(3) inv5_def)
        hence \<open>\<not>(not_every_vote_counted procs (find_vote (events @ [(0, event)])))\<close>
          using key by auto
        hence ult2:\<open>inv5 procs (events @ [(0,event)]) states'\<close> using inv5_def by auto
        have \<open>inv6 procs (events @ [(0,event)]) states'\<close>
          by (simp add: Value \<open>states' 0 = states 0\<close> inv6_def)
        thus ?thesis using ult1 ult2 by auto
      next
        case (Vote_Count f) (* f decides to Value val after vote v *)
        hence knowf:\<open>f = find_vote events\<close>
          using assms(3) inv6_def by auto
        moreover have \<open>not_every_vote_counted procs (find_vote events)\<close>
          using assms(3) inv6_def Vote_Count by blast
        ultimately have fdonebefore:\<open>(not_every_vote_counted procs f)\<close>
          by auto
        from this obtain p where \<open>p\<in>procs \<and> f p = None \<and> p \<noteq> 0\<close>
          by auto
        hence b:\<open>\<not> (procs \<union> {sender} \<subseteq> {0})\<close> by auto
        have senderNone:\<open>find_vote events sender = None\<close>
        proof (cases \<open>find_vote events sender\<close>)
          case None
          then show ?thesis by auto
        next
          case (Some uu) (* this case leads to a contradiction *)
          hence \<open>f sender = Some uu\<close>
            using knowf by simp
          hence knowcount:\<open>count_update procs f sender v = (Vote_Count f , {})\<close>
            using count_update.simps by auto
          hence h:\<open>acceptor_step procs (Vote_Count f) (Receive sender (Propose v))
                       = (Vote_Count f, {})\<close> by simp
          have \<open>event = Receive sender (Propose v)\<close>
            by (simp add: Propose Receive)
          hence \<open>(consensus_step procs 0 (states 0) event) = (Vote_Count f , {})\<close>
            using Vote_Count h by simp
          hence \<open>states' 0 = Vote_Count f\<close>
            using assms(1) assms(2) by simp
          hence \<open>False\<close>
            using Value by auto
          then show ?thesis by auto
        qed
        hence senderNone2: \<open>f sender = None\<close> using knowf by simp
        have fdone:\<open>\<not>(not_every_vote_counted procs (f(sender := Some v)))\<close>
        proof (rule ccontr)
          assume \<open>\<not> \<not> not_every_vote_counted procs (f(sender := Some v))\<close>
          hence \<open>not_every_vote_counted procs (f(sender := Some v))\<close> by auto
          hence \<open>count_update procs f sender v = (Vote_Count (f (sender := Some v)), {})\<close>
            using senderNone2 count_update.simps by auto
          hence h:\<open>acceptor_step procs (Vote_Count f) (Receive sender (Propose v))
                       = (Vote_Count (f (sender := Some v)), {})\<close> by simp
          have \<open>event = Receive sender (Propose v)\<close>
            by (simp add: Propose Receive)
          hence \<open>(consensus_step procs 0 (states 0) event) = (Vote_Count (f (sender := Some v)), {})\<close>
            using Vote_Count h by simp
          hence \<open>states' 0 = Vote_Count (f (sender := Some v))\<close>
            using assms(1) assms(2) by simp
          thus \<open>False\<close> using Value by auto
        qed
        hence isdone:\<open>\<not>(not_every_vote_counted procs ((find_vote events)(sender := Some v)))\<close>
          using knowf by simp
        have a1:\<open>find_vote [(0,event)] sender = Some v\<close>
          using Receive Propose by auto
        (*have \<open>\<exists>a.(fst a =0 \<and> snd a = event)\<close> by auto
        from this obtain a where \<open>fst a =0 \<and> snd a = event\<close> by auto
        have \<open>find_vote (events @ [a]) sender = find_vote [a] sender\<close>
          using find_vote_lemma3wtf[where ?x = events and ?p = sender] senderNone by auto*)
        have \<open>find_vote (events @ [(0,event)]) sender = find_vote [(0,event)] sender\<close>
          using find_vote_lemma3type[where ?x = events and ?p = sender and ?q=0 and ?event=event]
                senderNone by (metis a1)
        (* have \<open>find_vote (events @ [(0,event)]) sender = find_vote [(0,event)] sender\<close>
          using find_vote_lemma3[where ?x = events and ?p = sender] senderNone by auto *)
        hence knowsendervote:\<open>find_vote (events @ [(0,event)]) sender = Some v\<close>
          by (simp only: a1)
        (*moreover have knowothervotes:\<open>p\<noteq>sender \<Longrightarrow> find_vote (events @ [(0,event)]) p = find_vote events p\<close>
          using Receive find_vote_nonsender Propose by fastforce*)
        have asdf:\<open>find_vote (events @ [(0,event)]) = (find_vote events) (sender:= Some v)\<close>
        proof
          fix p
          show \<open>find_vote (events @ [(0, event)]) p = (find_vote events(sender \<mapsto> v)) p\<close>
          proof(cases \<open>p=sender\<close>)
            case True
            then show ?thesis using knowsendervote by auto
          next
            case False
            hence \<open>find_vote (events @ [(0,event)]) p = find_vote events p\<close>
              using Receive find_vote_nonsender Propose by fastforce
            moreover have \<open>find_vote events p = (find_vote events(sender \<mapsto> v)) p\<close>
              using False by auto
            ultimately show ?thesis by simp
          qed
        qed
        hence finalvote:\<open>find_vote (events @ [(0,event)]) = (f(sender:= Some v))\<close>
          using knowf by simp
        hence votedone:\<open>\<not>(not_every_vote_counted procs (find_vote (events @ [(0,event)])))\<close>
          using asdf Receive Propose isdone by auto
        have i5:\<open>inv5 procs (events @ [(0,event)]) states'\<close>
          using votedone inv5_def by auto
        let ?somew = \<open>pick_winner (procs\<union>{sender}) (f (sender := Some v))\<close>
        have b0:\<open>\<not> not_every_vote_counted (procs \<union> {sender}) (f(sender \<mapsto> v))\<close>
          using fdone by auto
        moreover have b2:\<open>finite (procs \<union> {sender})\<close>
          using assms(7) by auto
        ultimately have somewin:\<open>?somew \<in> set_of_potential_winners (procs \<union> {sender}) (f(sender := Some v))\<close>
          using b winnerispotential[where ?procs=\<open>procs\<union>{sender}\<close> and ?f=\<open>f (sender := Some v)\<close>] by auto
        obtain vvv where \<open>?somew = Some vvv\<close>
          using b0 b b2 winnersome[where ?procs=\<open>procs\<union>{sender}\<close> and ?f=\<open>f (sender := Some v)\<close>] by auto
        let ?w = \<open>the (pick_winner (procs\<union>{sender}) (f (sender := Some v)))\<close>
        have \<open>vvv=?w\<close>
          by (metis \<open>pick_winner (procs \<union> {sender}) (f(sender \<mapsto> v)) = Some vvv\<close> option.sel)
        have valwins:\<open>val=?w\<close>
        proof(rule ccontr)
          assume a:\<open>val\<noteq>?w\<close>
          have \<open>count_update procs f sender v = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close>
            using senderNone2 fdone count_update.simps by (smt (verit, best) option.case_eq_if)
          hence h:\<open>acceptor_step procs (Vote_Count f) (Receive sender (Propose v))
                       = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close> by simp
          have \<open>event = Receive sender (Propose v)\<close>
            by (simp add: Propose Receive)
          hence \<open>(consensus_step procs 0 (states 0) event) = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close>
            using Vote_Count h by simp
          hence \<open>states' 0 = Value ?w\<close>
            using assms(1) assms(2) by simp
          moreover have \<open>states' 0 \<noteq> Value ?w\<close> using Value a by auto
          ultimately show \<open>False\<close> by auto
        qed
        hence \<open>Some val = ?somew\<close>
          using \<open>?somew = Some vvv\<close> \<open>vvv = ?w\<close> by simp
        hence \<open>Some val \<in> set_of_potential_winners (procs \<union> {sender}) (f(sender := Some v))\<close>
          by (simp only:somewin)
        hence qwerty:\<open>Some val \<in> set_of_potential_winners (procs \<union> {sender}) (find_vote (events @ [(0,event)]))\<close>
          using finalvote by simp
        have \<open>not_every_vote_counted procs (find_vote events)\<close>
          using assms(3) inv6_def Vote_Count by blast
        hence \<open>sender \<in> procs\<close>
          using isdone by (metis (mono_tags, lifting) fun_upd_other not_every_vote_counted.simps)
        hence \<open>procs \<union> {sender} = procs\<close>
          by auto
        hence \<open>Some val \<in> set_of_potential_winners procs (find_vote (events @ [(0,event)]))\<close>
          using qwerty by simp
        hence i4:\<open>inv4 procs (events @ [(0,event)]) states'\<close>
          by (metis Value inv4_def state.inject(1))
        have \<open>\<forall>ff.(states' 0 \<noteq> Vote_Count ff)\<close>
          using Value by auto
        hence \<open>inv6 procs (events @ [(0,event)]) states'\<close>
          using inv6_def by blast
        then show ?thesis using i4 i5 by auto
      qed
    next
      case vcf:(Vote_Count f) (* msg=Receive (Propose val) and states'0 = Vote_Count f *)
      hence i4i5:\<open>inv4 procs (events @ [(0,event)]) states' \<and> inv5 procs (events @ [(0,event)]) states'\<close>
        by (simp add: inv4_def inv5_def)
      have \<open>inv6 procs (events @ [(0,event)]) states'\<close>
      proof (cases \<open>states 0\<close>)
        case Nothing
        hence knowfind:\<open>find_vote events = initial_vote_count\<close>
          using assms(6) inv8_def invs8 by blast
        have n:\<open>initial_vote_count sender = None\<close> by auto
        have notgafter:\<open>not_every_vote_counted procs (initial_vote_count(sender:= Some v))\<close>
        proof (rule ccontr)
          assume as:\<open>\<not>not_every_vote_counted procs (initial_vote_count(sender:= Some v))\<close>
          let ?w = \<open>the (pick_winner (procs\<union>{sender}) (initial_vote_count (sender := Some v)))\<close>
          have \<open>count_update procs initial_vote_count sender v = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close>
            using as n count_update.simps by (smt (verit, best) option.case_eq_if)
          hence h:\<open>acceptor_step procs (Vote_Count initial_vote_count) (Receive sender (Propose v))
                     = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close> by simp
          have \<open>event = Receive sender (Propose v)\<close>
            by (simp add: Propose Receive)
          hence \<open>(consensus_step procs 0 (states 0) event) = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close>
            using Nothing h by simp
          hence \<open>states' 0 = Value ?w\<close>
            using assms(1) assms(2) by simp
          moreover have \<open>states' 0 \<noteq> Value ?w\<close> using vcf by auto
          ultimately show \<open>False\<close> by auto
        qed
        hence \<open>count_update procs initial_vote_count sender v = (Vote_Count (initial_vote_count(sender:= Some v)) , {})\<close>
          using n count_update.simps Propose Receive by auto
        hence \<open>(acceptor_step procs (Vote_Count initial_vote_count) (Receive sender (Propose v))) = (Vote_Count (initial_vote_count(sender:= Some v)), {})\<close>
          using Propose Receive by simp
        hence \<open>(consensus_step procs 0 (states 0) (Receive sender (Propose v))) = (Vote_Count (initial_vote_count(sender:= Some v)), {})\<close>
          using Nothing by auto
        moreover have \<open>event = Receive sender (Propose v)\<close>
          by (simp add: Propose Receive)
        ultimately have \<open>new_state = Vote_Count (initial_vote_count(sender:= Some v))\<close>
          using assms(1) by auto
        hence \<open>states' 0 = Vote_Count (initial_vote_count(sender:= Some v))\<close>
          using assms(2) by auto
        hence \<open>Vote_Count f = Vote_Count (initial_vote_count(sender:= Some v))\<close>
          using vcf by auto
        hence gtof:\<open>f = (initial_vote_count(sender:= Some v))\<close> by auto
        have hh:\<open>find_vote (events @ [(0,event)]) = (find_vote events)(sender:= Some v)\<close>
        proof
          fix p
          show \<open>find_vote (events @ [(0,event)]) p = ((find_vote events)(sender:= Some v)) p\<close>
          proof(cases \<open>p=sender\<close>)
            case True
            have hhh:\<open>find_vote events sender = None\<close>
              using knowfind n by simp
            have a1:\<open>find_vote [(0,event)] sender = Some v\<close>
              using Receive Propose by auto
            have \<open>find_vote (events @ [(0,event)]) sender = find_vote [(0,event)] sender\<close>
              using find_vote_lemma3type[where ?x = events and ?p = sender and ?q=0 and ?event=event]
                hhh by (metis a1)
            hence \<open>find_vote (events @ [(0, event)]) sender = Some v\<close>
              using Receive Propose by fastforce
            moreover have \<open>((find_vote events)(sender:= Some v)) sender = Some v\<close>
              by auto
            ultimately show ?thesis
              using True by simp
          next
            case False
            then show ?thesis
              by (simp add: Propose Receive find_vote_nonsender)
          qed
        qed
        hence u1:\<open>f = find_vote (events @ [(0,event)])\<close>
          using knowfind hh gtof by auto
        hence u2:\<open>not_every_vote_counted procs (find_vote (events @ [(0,event)]))\<close>
          using notgafter hh gtof by auto
        then show \<open>inv6 procs (events @ [(0,event)]) states'\<close>
          using u1 u2 inv6_def vcf by fastforce
      next
        case (Value u)
        then show ?thesis
          by (metis assms(1) assms(2) fun_upd_same state.distinct(5) state_value_does_not_change vcf)
      next
        case (Vote_Count g)
        hence knowg:\<open>g = find_vote events\<close>
          using assms(6) inv6_def assms(3) by blast
        have notbefore:\<open>not_every_vote_counted procs (find_vote events)\<close>
          using assms(3) inv6_def Vote_Count by blast
        hence notg:\<open>not_every_vote_counted procs g\<close>
          using knowg by auto
        show ?thesis
        proof (cases \<open>g sender\<close>)
          case n:None
          have notgafter:\<open>not_every_vote_counted procs (g(sender:= Some v))\<close>
          proof (rule ccontr)
            assume as:\<open>\<not>not_every_vote_counted procs (g(sender:= Some v))\<close>
            let ?w = \<open>the (pick_winner (procs\<union>{sender}) (g (sender := Some v)))\<close>
            have \<open>count_update procs g sender v = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close>
              using as n count_update.simps by (smt (verit, best) option.case_eq_if)
            hence h:\<open>acceptor_step procs (Vote_Count g) (Receive sender (Propose v))
                       = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close> by simp
            have \<open>event = Receive sender (Propose v)\<close>
              by (simp add: Propose Receive)
            hence \<open>(consensus_step procs 0 (states 0) event) = set_value_and_send_accept_all (procs\<union>{sender}) ?w\<close>
              using Vote_Count h by simp
            hence \<open>states' 0 = Value ?w\<close>
              using assms(1) assms(2) by simp
            moreover have \<open>states' 0 \<noteq> Value ?w\<close> using vcf by auto
            ultimately show \<open>False\<close> by auto
          qed
          hence \<open>count_update procs g sender v = (Vote_Count (g(sender:= Some v)) , {})\<close>
            using n count_update.simps Propose Receive by auto
          hence \<open>(acceptor_step procs (Vote_Count g) (Receive sender (Propose v))) = (Vote_Count (g(sender:= Some v)), {})\<close>
            using Propose Receive by simp
          hence \<open>(consensus_step procs 0 (states 0) (Receive sender (Propose v))) = (Vote_Count (g(sender:= Some v)), {})\<close>
            using Vote_Count by auto
          moreover have \<open>event = Receive sender (Propose v)\<close>
            by (simp add: Propose Receive)
          ultimately have \<open>new_state = Vote_Count (g(sender:= Some v))\<close>
            using assms(1) by auto
          hence \<open>states' 0 = Vote_Count (g(sender:= Some v))\<close>
            using assms(2) by auto
          hence \<open>Vote_Count f = Vote_Count (g(sender:= Some v))\<close>
            using vcf by auto
          hence gtof:\<open>f = (g(sender:= Some v))\<close> by auto
          have hh:\<open>find_vote (events @ [(0,event)]) = (find_vote events)(sender:= Some v)\<close>
          proof
            fix p
            show \<open>find_vote (events @ [(0,event)]) p = ((find_vote events)(sender:= Some v)) p\<close>
            proof(cases \<open>p=sender\<close>)
              case True
              have hhh:\<open>find_vote events sender = None\<close>
                using knowg n by simp
              have a1:\<open>find_vote [(0,event)] sender = Some v\<close>
                using Receive Propose by auto
              have \<open>find_vote (events @ [(0,event)]) sender = find_vote [(0,event)] sender\<close>
                using find_vote_lemma3type[where ?x = events and ?p = sender and ?q=0 and ?event=event]
                      hhh by (metis a1)
              hence \<open>find_vote (events @ [(0, event)]) sender = Some v\<close>
                using Receive Propose by fastforce
              moreover have \<open>((find_vote events)(sender:= Some v)) sender = Some v\<close>
                by auto
              ultimately show ?thesis
                using True by simp
            next
              case False
              then show ?thesis
                by (simp add: Propose Receive find_vote_nonsender)
            qed
          qed
          hence u1:\<open>f = find_vote (events @ [(0,event)])\<close>
            using knowg hh gtof by auto
          hence u2:\<open>not_every_vote_counted procs (find_vote (events @ [(0,event)]))\<close>
            using notgafter hh gtof by auto
          then show \<open>inv6 procs (events @ [(0,event)]) states'\<close>
            using u1 u2 inv6_def vcf by fastforce
        next
          case somevv:(Some vv)
          hence \<open>count_update procs g sender v = (Vote_Count g , {})\<close>
            using count_update.simps by auto
          hence \<open>(acceptor_step procs (Vote_Count g) (Receive sender (Propose v))) = (Vote_Count g, {})\<close>
            using Propose Receive by simp
          hence \<open>(consensus_step procs 0 (states 0) (Receive sender (Propose v))) = (Vote_Count g, {})\<close>
            using Vote_Count by auto
          moreover have \<open>event = Receive sender (Propose v)\<close>
            by (simp add: Propose Receive)
          ultimately have \<open>new_state = Vote_Count g\<close>
            using assms(1) by auto
          hence \<open>states' 0 = Vote_Count g\<close>
            using assms(2) by auto
          hence \<open>Vote_Count f = Vote_Count g\<close>
            using vcf by auto
          hence \<open>f=g\<close> by auto
          have hh:\<open>find_vote (events @ [(0,event)]) = find_vote events\<close>
          proof
            fix p
            show \<open>find_vote (events @ [(0,event)]) p = find_vote events p\<close>
            proof(cases \<open>p=sender\<close>)
              case True
              have hhh:\<open>find_vote events sender = Some vv\<close>
                using knowg somevv by simp
              hence \<open>find_vote (events @ [(0, event)]) sender = Some vv\<close>
                using find_vote_lemma1 by fastforce
              hence \<open>find_vote (events @ [(0, event)]) sender = find_vote events sender\<close>
                using hhh by simp
              then show ?thesis
                using True by simp
            next
              case False
              then show ?thesis
                by (simp add: Propose Receive find_vote_nonsender)
            qed
          qed
          hence u1:\<open>f = find_vote (events @ [(0,event)])\<close>
            using knowg \<open>f=g\<close> by auto
          have u2:\<open>not_every_vote_counted procs (find_vote (events @ [(0,event)]))\<close>
            using notbefore hh by auto
          then show \<open>inv6 procs (events @ [(0,event)]) states'\<close>
            using u1 u2 inv6_def vcf by fastforce
        qed
      qed
      then show ?thesis using i4i5 by auto
    qed
  next
    case (Accept w)
    thus ?thesis
    proof (cases \<open>states 0\<close>)
      case Nothing
      hence \<open>states' 0 = Nothing\<close>
        using Accept Receive assms(1) assms(2) by auto
      then show ?thesis
        by (simp add: inv4_def inv5_def inv6_def)
    next
      case (Value val)
      hence key:\<open>\<And>pp. (pp\<in>procs\<and>pp\<noteq>0 \<Longrightarrow>find_vote (events @ [(0, event)]) pp = find_vote events pp)\<close>
        using find_vote_already_done by (metis assms(3))
      hence key2:\<open>\<And>pp val.((pp\<in>procs) \<Longrightarrow> ((find_vote (events @ [(0,event)])) pp = val \<and> pp\<noteq>0) \<longleftrightarrow> ((find_vote events) pp = val) \<and> pp\<noteq>0)\<close>
        by auto
      hence \<open>\<And> val. (\<exists>pp\<in>procs. (find_vote (events @ [(0,event)])) pp = val \<and> pp \<noteq> 0) \<longleftrightarrow> (\<exists>pp\<in>procs. (find_vote events) pp = val \<and> pp \<noteq> 0)\<close>
        by auto
      hence \<open>{val.(\<exists>pp\<in>procs. (find_vote (events @ [(0,event)])) pp = val \<and> pp \<noteq> 0)} = {val.(\<exists>pp\<in>procs. (find_vote events) pp = val \<and> pp \<noteq> 0)}\<close>
        by auto
      hence hvals:\<open>vals_with_votes procs (find_vote (events @ [(0, event)])) = vals_with_votes procs (find_vote events)\<close>
        by auto
      have \<open>\<And>val.({pp\<in> procs . (find_vote (events @ [(0, event)])) pp = val \<and> pp\<noteq>0}={pp\<in> procs . (find_vote events) pp = val \<and> pp\<noteq>0})\<close>
        using key2 by auto
      hence hh:\<open>nonzero_counter procs (find_vote (events @ [(0, event)])) = nonzero_counter procs (find_vote events)\<close>
        by auto
      hence \<open>most_vote_counts procs (find_vote (events @ [(0, event)])) = most_vote_counts procs (find_vote events)\<close>
        using hvals by auto
      hence \<open>set_of_potential_winners procs (find_vote (events @ [(0, event)]))
              = set_of_potential_winners procs (find_vote events)\<close>
        using hh by auto
      moreover have \<open>states' 0 = states 0\<close> using Receive Accept assms by auto
      ultimately have ult1:\<open>inv4 procs (events @ [(0,event)]) states'\<close>
        using inv4_def by (metis assms(3))
      have \<open>\<not>(not_every_vote_counted procs (find_vote events))\<close>
        by (meson Value assms(3) inv5_def)
      hence \<open>\<not>(not_every_vote_counted procs (find_vote (events @ [(0, event)])))\<close>
        using key by auto
      hence ult2:\<open>inv5 procs (events @ [(0,event)]) states'\<close> using inv5_def by auto
      hence i4i5:\<open>inv4 procs (events @ [(0,event)]) states' \<and> inv5 procs (events @ [(0,event)]) states'\<close>
        using ult1 ult2 by auto
      have \<open>find_vote (events @ [(0,event)]) = find_vote events\<close>
        using Receive Accept find_vote_accept by auto
      hence \<open>inv6 procs (events @ [(0,event)]) states'\<close>
        by (simp add: Value \<open>states' 0 = states 0\<close> inv6_def)
      then show ?thesis using i4i5 by auto
    next
      case (Vote_Count f)
      hence \<open>states' 0 = Vote_Count f\<close>
        using Accept Receive assms(1) assms(2) by auto
      hence i4i5:\<open>inv4 procs (events @ [(0,event)]) states' \<and> inv5 procs (events @ [(0,event)]) states'\<close>
        by (simp add: inv4_def inv5_def)
      have \<open>find_vote (events @ [(0,event)]) = find_vote events\<close>
        using Receive Accept find_vote_accept by auto
      hence \<open>inv6 procs (events @ [(0,event)]) states'\<close>
        by (metis Vote_Count \<open>states' 0 = Vote_Count f\<close> assms(3) inv6_def)
      then show ?thesis using i4i5 by auto
    qed
  qed
next
  case (Request v)
  then show ?thesis
    using assms inv4_request inv5_request inv6_request by auto
next
  case Timeout
  then show ?thesis
    using assms inv4_timeout inv5_timeout inv6_timeout by auto
qed

lemma invs456:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
    and \<open>finite procs\<close>
  shows \<open>inv4 procs events states \<and> inv5 procs events states \<and> inv6 procs events states\<close>
  using  assms
proof(induction events arbitrary: msgs states rule: List.rev_induct)
  case Nil
  from this show \<open>inv4 procs [] states \<and> inv5 procs [] states \<and> inv6 procs [] states\<close>
    using execute_init inv4_def inv5_def inv6_def by fastforce
next
  case (snoc x events)
  obtain proc event where \<open>x = (proc, event)\<close>
    by fastforce
  hence exec: \<open>execute consensus_step (\<lambda>p. Nothing) procs
               (events @ [(proc, event)]) msgs states\<close>
    using snoc.prems by blast
  from this obtain msgs' states' sent new_state
    where step_rel1: \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs' states'\<close>
      and step_rel2: \<open>consensus_step procs proc (states' proc) event = (new_state, sent)\<close>
      and step_rel3: \<open>msgs = msgs' \<union> ((\<lambda>msg. (proc, msg)) ` sent)\<close>
      and step_rel4: \<open>states = states' (proc := new_state)\<close>
    by auto
  have inv_before: \<open>inv4 procs events states' \<and> inv5 procs events states' \<and> inv6 procs events states'\<close>
    using snoc.IH step_rel1 assms(2) by fastforce
  then show \<open>inv4 procs (events @ [x]) states \<and> inv5 procs (events @ [x]) states \<and> inv6 procs  (events @ [x]) states\<close>
  proof (cases \<open>proc = 0\<close>)
    case True
    then show ?thesis
      by (metis assms(2) \<open>x = (proc, event)\<close> anotherinv456pzero exec inv_before step_rel1 step_rel2 step_rel3 step_rel4)
next
    case False
    then show ?thesis
      using \<open>x = (proc, event)\<close> anotherinv456pnonzero inv_before step_rel2 step_rel4
      by (metis exec fun_upd_other)
  qed
qed

lemma pre_only_winners:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
    and \<open>finite procs\<close>
  shows \<open>(\<forall>val. (states 0 = Value val \<longrightarrow> Some val \<in> set_of_potential_winners procs (find_vote events)))
          \<or>(procs\<subseteq>{0})\<close>
  using invs456 inv4_def by (metis assms)

lemma only_winners:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
    and \<open>states 0 = Value val\<close>
    and \<open>finite procs\<close>
  shows \<open>(Some val \<in> set_of_potential_winners procs (find_vote events))
          \<or>(procs\<subseteq>{0})\<close>
  using assms pre_only_winners by blast

lemma voting_done:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
    and \<open>states 0 = Value val\<close>
    and \<open>finite procs\<close>
  shows \<open>\<not>(not_every_vote_counted procs (find_vote events))\<close>
  by (meson assms inv5_def invs456)

lemma acceptor_first:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
    and \<open>states p = Value val\<close>
  shows \<open>states 0 = Value val\<close>
    by (metis assms(1) assms(2) inv1_def inv2_def invariants)

theorem fairness:
  assumes \<open>execute consensus_step (\<lambda>x. Nothing) procs events msgs states\<close>
    and \<open>states proc = Value val\<close>
    and \<open>finite procs\<close>
  shows \<open>(\<not>(not_every_vote_counted procs (find_vote events))
          \<and> Some val \<in> set_of_potential_winners procs (find_vote events))
         \<or>(procs\<subseteq>{0})\<close>
  using only_winners voting_done acceptor_first
  by (metis assms)

end