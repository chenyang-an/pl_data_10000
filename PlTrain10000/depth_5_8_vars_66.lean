variable (p0 p5 p1 p7 p4 p3 p2 : Prop)
theorem file66_47 : (((((p2 ∧ False) ∨ (p7 → False)) ∧ ((p5 ∧ p5) ∧ (p2 → p1))) ∨ (((p1 ∧ p1) ∨ (p3 ∧ p0)) → ((p2 → False) → (p0 ∨ p4)))) → ((((p5 ∨ p3) ∨ (True ∨ p0)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          apply False.elim assump_12
      case inr assump_10 =>
        cases assump_8
        case intro assump_19 assump_20 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            have assump_44 : ((p5 ∨ p3) ∨ (True ∨ p0)) := by
              apply Or.inl
              apply Or.inl
              exact assump_22
            let assump_33 := assump_2 assump_44
            apply False.elim assump_33
  case inr assump_6 =>
    have assump_45 : ((p5 ∨ p3) ∨ (True ∨ p0)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_40 := assump_2 assump_45
    apply False.elim assump_40


variable (p3 p5 p0 p7 p4 p2 : Prop)
theorem file66_1162 : (((((p7 ∨ p7) → (p5 ∨ p2)) ∨ ((p7 ∨ p3) → False)) → (((p0 ∨ True) ∨ (p0 ∨ p0)) ∧ ((False ∨ p4) ∨ (p7 ∨ True)))) ∨ ((((True → p5) ∨ (p0 → True)) → ((p3 ∨ p2) → (True → False))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  cases assump_1
  case inl assump_8 =>
    apply Or.inr
    apply Or.inr
    apply True.intro
  case inr assump_9 =>
    apply Or.inr
    apply Or.inr
    apply True.intro


variable (p1 p3 p0 p2 p5 p7 p6 p4 : Prop)
theorem file66_1816 : ((((((True ∨ p0) → (p1 → p3)) ∧ ((p6 → False) → False)) ∨ (((p2 → p6) → (p0 ∨ False)) → False)) ∧ ((((p5 → p7) → False) ∧ ((False ∧ p4) ∧ (p1 → False))) ∧ (((p4 → False) ∨ (p7 ∧ p4)) → ((True → False) ∨ (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
    case inr assump_5 =>
      cases assump_3
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_29
          case intro assump_32 assump_33 =>
            cases assump_32
            case intro assump_34 assump_35 =>
              apply False.elim assump_34


variable (p3 p6 p2 p0 p5 p4 : Prop)
theorem file66_2951 : ((((((p3 → False) → False) → ((p5 ∧ p2) → False)) ∧ (((False → False) ∨ (False ∨ p5)) → False)) ∨ ((((p4 ∨ p4) → (p4 ∨ p0)) → ((p4 ∧ False) ∧ (p3 ∧ False))) ∨ (((False ∧ p2) → (p6 → p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_49 : ((False → False) ∨ (False ∨ p5)) := by
        apply Or.inl
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_5 assump_49
      apply False.elim assump_10
  case inr assump_3 =>
    cases assump_3
    case inl assump_17 =>
      have assump_50 : ((p4 ∨ p4) → (p4 ∨ p0)) := by
        intro assump_22
        cases assump_22
        case inl assump_23 =>
          apply Or.inl
          exact assump_23
        case inr assump_24 =>
          apply Or.inl
          exact assump_24
      let assump_21 := assump_17 assump_50
      let assump_29 := And.left assump_21
      let assump_30 := And.right assump_29
      apply False.elim assump_30
    case inr assump_18 =>
      have assump_51 : ((False ∧ p2) → (p6 → p6)) := by
        intro assump_38
        intro assump_39
        cases assump_38
        case intro assump_42 assump_43 =>
          apply False.elim assump_42
      let assump_37 := assump_18 assump_51
      apply False.elim assump_37


variable (p6 p5 p7 p2 p1 p4 : Prop)
theorem file66_4350 : (((((p2 → False) ∧ (p4 ∨ True)) ∨ ((p7 → False) ∨ (p5 → p5))) ∨ (((p4 ∨ False) → False) ∨ ((p2 ∧ True) → False))) → ((((p7 → p1) ∨ (True ∨ False)) → False) → (((p6 ∧ p1) ∧ (p5 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_1
      case inl assump_16 =>
        cases assump_16
        case inl assump_18 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_21
            case inl assump_24 =>
              have assump_91 : ((p7 → p1) ∨ (True ∨ False)) := by
                apply Or.inl
                intro assump_31
                exact assump_7
              let assump_30 := assump_2 assump_91
              apply False.elim assump_30
            case inr assump_25 =>
              have assump_92 : ((p7 → p1) ∨ (True ∨ False)) := by
                apply Or.inl
                intro assump_41
                exact assump_7
              let assump_40 := assump_2 assump_92
              apply False.elim assump_40
        case inr assump_19 =>
          cases assump_19
          case inl assump_47 =>
            have assump_93 : ((p7 → p1) ∨ (True ∨ False)) := by
              apply Or.inl
              intro assump_53
              exact assump_7
            let assump_52 := assump_2 assump_93
            apply False.elim assump_52
          case inr assump_48 =>
            have assump_94 : ((p7 → p1) ∨ (True ∨ False)) := by
              apply Or.inl
              intro assump_63
              exact assump_7
            let assump_62 := assump_2 assump_94
            apply False.elim assump_62
      case inr assump_17 =>
        cases assump_17
        case inl assump_69 =>
          have assump_95 : ((p7 → p1) ∨ (True ∨ False)) := by
            apply Or.inl
            intro assump_75
            exact assump_7
          let assump_74 := assump_2 assump_95
          apply False.elim assump_74
        case inr assump_70 =>
          have assump_96 : ((p7 → p1) ∨ (True ∨ False)) := by
            apply Or.inl
            intro assump_85
            exact assump_7
          let assump_84 := assump_2 assump_96
          apply False.elim assump_84


variable (p2 p6 p4 p3 : Prop)
theorem file66_6687 : (((((p2 ∨ p3) ∧ (False ∧ p6)) ∨ ((False → False) ∨ (p4 → False))) → (((True → False) → (p3 ∨ p4)) → False)) → False) := by
  intro assump_1
  have assump_19 : (((p2 ∨ p3) ∧ (False ∧ p6)) ∨ ((False → False) ∨ (p4 → False))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_19
  have assump_20 : ((True → False) → (p3 ∨ p4)) := by
    intro assump_9
    have assump_21 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_21
    apply False.elim assump_12
  let assump_8 := assump_4 assump_20
  apply False.elim assump_8


variable (p0 p7 p6 p2 : Prop)
theorem file66_7354 : (((((p7 → False) → (p7 → False)) → False) ∨ (((p0 → False) ∧ (p0 ∧ p6)) ∧ ((p2 → p7) ∧ (False → False)))) → ((((False → False) → False) → False) → (((True → p0) → (p6 ∧ p7)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    have assump_52 : ((p7 → False) → (p7 → False)) := by
      intro assump_13
      intro assump_14
      have assump_53 : p7 := by
        exact assump_14
      let assump_19 := assump_13 assump_53
      apply False.elim assump_19
    let assump_12 := assump_8 assump_52
    apply False.elim assump_12
  case inr assump_9 =>
    cases assump_9
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_29
        case intro assump_32 assump_33 =>
          cases assump_27
          case intro assump_38 assump_39 =>
            have assump_54 : p0 := by
              exact assump_32
            let assump_48 := assump_28 assump_54
            apply False.elim assump_48


variable (p2 p1 p6 p5 p0 p3 : Prop)
theorem file66_8434 : ((((((p3 ∧ p1) ∧ (p1 → False)) → ((p0 ∨ p0) → False)) ∨ (((p6 → p2) → (p5 → False)) ∨ ((p0 → False) → (p1 → p3)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p3 ∧ p1) ∧ (p1 → False)) → ((p0 ∨ p0) → False)) ∨ (((p6 → p2) → (p5 → False)) ∨ ((p0 → False) → (p1 → p3)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_45 : p1 := by
            exact assump_14
          let assump_21 := assump_12 assump_45
          apply False.elim assump_21
    case inr assump_8 =>
      cases assump_5
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          have assump_46 : p1 := by
            exact assump_30
          let assump_37 := assump_28 assump_46
          apply False.elim assump_37
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p2 p4 p7 p3 p0 : Prop)
theorem file66_9524 : (((((p3 → False) ∧ (p2 → False)) → ((p7 ∧ p7) → (p4 ∨ p3))) ∧ (((False → p0) → (p3 → p3)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : ((False → p0) → (p3 → p3)) := by
      intro assump_9
      intro assump_10
      exact assump_10
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p4 p1 p6 p0 p2 p3 : Prop)
theorem file66_9955 : ((((((p0 → False) ∨ (p0 → p4)) → ((False ∨ False) → (p2 → False))) ∨ (((p6 ∨ p4) ∧ (p4 ∧ p4)) → ((p3 → p4) → (False ∧ p1)))) → False) → False) := by
  intro assump_5
  have assump_23 : ((((p0 → False) ∨ (p0 → p4)) → ((False ∨ False) → (p2 → False))) ∨ (((p6 ∨ p4) ∧ (p4 ∧ p4)) → ((p3 → p4) → (False ∧ p1)))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_10
    case inl assump_14 =>
      apply False.elim assump_14
    case inr assump_15 =>
      apply False.elim assump_15
  let assump_8 := assump_5 assump_23
  apply False.elim assump_8


variable (p2 p1 p0 p7 p6 p5 : Prop)
theorem file66_10608 : (((((False → False) → (p0 ∧ False)) ∧ ((False ∧ p2) ∧ (p1 ∧ True))) → False) ∨ ((((p2 → False) ∨ (p5 → p6)) ∨ ((p7 ∨ True) → (p1 → False))) ∨ (((p6 ∨ p6) → False) → ((p5 → False) ∧ (p1 → p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8


variable (p4 p7 p6 p5 p3 p1 : Prop)
theorem file66_11100 : ((((((p6 ∧ p5) → False) → False) ∧ (((False → False) → False) ∧ ((True ∧ p3) ∧ (p7 ∨ p5)))) ∨ ((((p1 ∧ p4) → False) → ((p7 ∧ p6) → (p7 ∨ p1))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_17
            case inl assump_24 =>
              have assump_64 : (False → False) := by
                intro assump_31
                apply False.elim assump_31
              let assump_30 := assump_12 assump_64
              apply False.elim assump_30
            case inr assump_25 =>
              have assump_65 : (False → False) := by
                intro assump_42
                apply False.elim assump_42
              let assump_41 := assump_12 assump_65
              apply False.elim assump_41
  case inr assump_7 =>
    have assump_66 : (((p1 ∧ p4) → False) → ((p7 ∧ p6) → (p7 ∨ p1))) := by
      intro assump_51
      intro assump_52
      cases assump_52
      case intro assump_53 assump_54 =>
        apply Or.inl
        exact assump_53
    let assump_50 := assump_7 assump_66
    apply False.elim assump_50


variable (p1 p7 p4 p0 p3 p2 p5 : Prop)
theorem file66_12496 : (((((p3 ∧ p2) → (p5 ∨ p5)) → ((True ∧ p4) ∨ (p3 → p3))) ∧ (((p0 → p7) ∨ (p5 ∨ p1)) → ((False ∨ p3) ∨ (True ∨ p3)))) → ((((p2 → False) → (p5 ∧ False)) → ((False ∧ p0) → (p0 ∧ p0))) ∨ (((p5 ∨ p7) → (True ∨ p4)) ∨ ((p3 → p7) ∨ (p4 ∧ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    apply And.intro
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
    cases assump_9
    case intro assump_14 assump_15 =>
      apply False.elim assump_14


variable (p0 p3 p4 p7 p5 : Prop)
theorem file66_13120 : ((((((p7 → p7) ∧ (False → p0)) ∨ ((p7 ∧ p3) → False)) ∨ (((p5 ∧ p4) → False) → False)) → False) → False) := by
  intro assump_11
  have assump_24 : ((((p7 → p7) ∧ (False → p0)) ∨ ((p7 ∧ p3) → False)) ∨ (((p5 ∧ p4) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    apply And.intro
    intro assump_15
    exact assump_15
    intro assump_18
    apply False.elim assump_18
  let assump_14 := assump_11 assump_24
  apply False.elim assump_14


variable (p2 p1 p5 p7 p4 p6 p0 p3 : Prop)
theorem file66_13638 : ((((((p3 → False) ∨ (p5 → False)) → False) ∨ (((p6 → p4) ∧ (p1 ∧ p4)) → False)) ∧ ((((False ∧ p0) ∧ (p7 → p0)) → ((False ∧ p0) → (p6 → p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_40 : (((False ∧ p0) ∧ (p7 → p0)) → ((False ∧ p0) → (p6 → p2))) := by
        intro assump_11
        intro assump_12
        intro assump_13
        cases assump_12
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
      let assump_10 := assump_3 assump_40
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_41 : (((False ∧ p0) ∧ (p7 → p0)) → ((False ∧ p0) → (p6 → p2))) := by
        intro assump_28
        intro assump_29
        intro assump_30
        cases assump_29
        case intro assump_33 assump_34 =>
          apply False.elim assump_33
      let assump_27 := assump_3 assump_41
      apply False.elim assump_27


variable (p3 p1 p5 p0 p2 p4 p7 p6 : Prop)
theorem file66_14681 : ((((((p6 → False) ∧ (p7 ∧ p2)) ∨ ((p7 → False) ∧ (p1 ∧ p4))) → (((p0 ∧ p5) ∨ (True ∨ True)) ∨ ((p7 → p3) ∧ (p4 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p6 → False) ∧ (p7 ∧ p2)) ∨ ((p7 → False) ∧ (p1 ∧ p4))) → (((p0 ∧ p5) ∨ (True ∨ True)) ∨ ((p7 → p3) ∧ (p4 ∨ True)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_18 assump_19 =>
        cases assump_19
        case intro assump_22 assump_23 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p2 p5 p1 p6 : Prop)
theorem file66_15639 : ((((((p6 → True) → False) → False) ∨ (((p1 → False) → (True ∨ p5)) → ((p2 → False) ∨ (p6 ∨ False)))) → False) → False) := by
  intro assump_19
  have assump_34 : ((((p6 → True) → False) → False) ∨ (((p1 → False) → (True ∨ p5)) → ((p2 → False) ∨ (p6 ∨ False)))) := by
    apply Or.inl
    intro assump_23
    have assump_35 : (p6 → True) := by
      intro assump_27
      apply True.intro
    let assump_26 := assump_23 assump_35
    apply False.elim assump_26
  let assump_22 := assump_19 assump_34
  apply False.elim assump_22


variable (p2 p7 p0 p1 p4 p5 : Prop)
theorem file66_16227 : (((((True → True) → False) ∧ ((p5 → True) ∧ (p2 → False))) ∧ (((p5 ∨ p0) ∧ (True ∨ p0)) → ((p5 → p1) ∧ (p0 ∨ p0)))) → ((((False ∨ p5) → (p5 ∨ p5)) → ((p1 ∧ p1) → False)) → (((p2 → False) ∧ (p7 → False)) ∨ ((p4 → p7) ∨ (p2 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply And.intro
        intro assump_19
        have assump_40 : p2 := by
          exact assump_19
        let assump_24 := assump_12 assump_40
        apply False.elim assump_24
        intro assump_28
        have assump_41 : (True → True) := by
          intro assump_36
          apply True.intro
        let assump_35 := assump_7 assump_41
        apply False.elim assump_35


variable (p0 p4 : Prop)
theorem file66_17124 : ((((((True → False) → (p0 → p4)) → False) → False) → False) → False) := by
  intro assump_20
  have assump_44 : ((((True → False) → (p0 → p4)) → False) → False) := by
    intro assump_24
    have assump_45 : ((True → False) → (p0 → p4)) := by
      intro assump_28
      intro assump_29
      have assump_46 : True := by
        apply True.intro
      let assump_34 := assump_28 assump_46
      apply False.elim assump_34
    let assump_27 := assump_24 assump_45
    apply False.elim assump_27
  let assump_23 := assump_20 assump_44
  apply False.elim assump_23


variable (p0 p3 p5 p7 p4 p1 p2 : Prop)
theorem file66_17749 : ((((((p3 ∧ False) → (p5 → p1)) ∨ ((p7 ∨ p5) ∧ (p5 ∨ p4))) → (((p0 ∧ p7) ∧ (p2 → False)) ∧ ((True ∨ p4) → False))) ∧ ((((p2 → False) ∨ (p0 ∨ p3)) ∧ ((p0 ∨ p2) → False)) ∨ (((True ∨ p0) → (p0 → True)) ∨ ((p2 ∨ p1) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          have assump_127 : (((p3 ∧ False) → (p5 → p1)) ∨ ((p7 ∨ p5) ∧ (p5 ∨ p4))) := by
            apply Or.inl
            intro assump_19
            intro assump_20
            cases assump_19
            case intro assump_23 assump_24 =>
              apply False.elim assump_24
          let assump_18 := assump_2 assump_127
          let assump_29 := And.right assump_18
          have assump_128 : (True ∨ p4) := by
            apply Or.inl
            apply True.intro
          let assump_35 := assump_29 assump_128
          apply False.elim assump_35
        case inr assump_11 =>
          cases assump_11
          case inl assump_39 =>
            have assump_129 : (p0 ∨ p2) := by
              apply Or.inl
              exact assump_39
            let assump_45 := assump_9 assump_129
            apply False.elim assump_45
          case inr assump_40 =>
            have assump_130 : (((p3 ∧ False) → (p5 → p1)) ∨ ((p7 ∨ p5) ∧ (p5 ∨ p4))) := by
              apply Or.inl
              intro assump_56
              intro assump_57
              cases assump_56
              case intro assump_60 assump_61 =>
                apply False.elim assump_61
            let assump_55 := assump_2 assump_130
            let assump_66 := And.right assump_55
            have assump_131 : (True ∨ p4) := by
              apply Or.inl
              apply True.intro
            let assump_72 := assump_66 assump_131
            apply False.elim assump_72
    case inr assump_7 =>
      cases assump_7
      case inl assump_76 =>
        have assump_132 : (((p3 ∧ False) → (p5 → p1)) ∨ ((p7 ∨ p5) ∧ (p5 ∨ p4))) := by
          apply Or.inl
          intro assump_83
          intro assump_84
          cases assump_83
          case intro assump_87 assump_88 =>
            apply False.elim assump_88
        let assump_82 := assump_2 assump_132
        let assump_93 := And.right assump_82
        have assump_133 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_99 := assump_93 assump_133
        apply False.elim assump_99
      case inr assump_77 =>
        have assump_134 : (((p3 ∧ False) → (p5 → p1)) ∨ ((p7 ∨ p5) ∧ (p5 ∨ p4))) := by
          apply Or.inl
          intro assump_107
          intro assump_108
          cases assump_107
          case intro assump_111 assump_112 =>
            apply False.elim assump_112
        let assump_106 := assump_2 assump_134
        let assump_117 := And.right assump_106
        have assump_135 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_123 := assump_117 assump_135
        apply False.elim assump_123


variable (p0 p2 p5 p1 p6 p4 p7 p3 : Prop)
theorem file66_20931 : ((((((p6 → False) → False) ∧ ((p6 ∧ p0) → False)) ∨ (((p5 → p6) → (p3 ∨ p2)) → ((p4 ∧ False) ∨ (p6 ∨ p7)))) ∧ ((((p5 ∨ p1) ∨ (p4 → p4)) ∨ ((p4 ∧ True) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_32 : (((p5 ∨ p1) ∨ (p4 → p4)) ∨ ((p4 ∧ True) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_15
          exact assump_15
        let assump_14 := assump_3 assump_32
        apply False.elim assump_14
    case inr assump_5 =>
      have assump_33 : (((p5 ∨ p1) ∨ (p4 → p4)) ∨ ((p4 ∧ True) → False)) := by
        apply Or.inl
        apply Or.inr
        intro assump_26
        exact assump_26
      let assump_25 := assump_3 assump_33
      apply False.elim assump_25


variable (p5 p3 p1 p4 p0 p2 : Prop)
theorem file66_21875 : ((((((p1 ∧ p3) ∨ (False ∧ True)) → ((False ∧ p2) → (p2 ∧ p0))) ∧ (((p1 ∨ True) → False) ∧ ((False ∧ False) → False))) ∧ ((((p1 ∨ True) ∨ (p5 → False)) ∧ ((p0 ∨ p4) ∧ (p1 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_22 : (p1 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_18 := assump_8 assump_22
        apply False.elim assump_18


variable (p5 p6 p7 p2 p4 p1 p0 p3 : Prop)
theorem file66_22501 : ((((((p2 ∨ p7) → (True ∨ p7)) ∨ ((p7 ∨ True) → False)) → False) ∧ ((((False ∨ False) ∧ (p5 ∧ p6)) → ((True ∧ p0) ∧ (p6 → p4))) ∧ (((p6 → True) ∨ (p3 → p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : ((p6 → True) ∨ (p3 → p1)) := by
        apply Or.inl
        intro assump_13
        apply True.intro
      let assump_12 := assump_7 assump_17
      apply False.elim assump_12


variable (p4 p6 p1 p3 p7 p0 : Prop)
theorem file66_23066 : ((((((p1 ∨ True) ∨ (p4 ∧ p4)) → False) ∧ (((p0 ∨ True) ∨ (p6 → False)) ∧ ((p3 → p0) ∨ (p7 → p1)))) ∧ ((((p4 ∧ False) → False) ∧ ((p4 → p0) ∧ (p7 ∨ False))) ∨ (((p6 ∨ True) ∨ (p7 ∨ p7)) ∨ ((p4 → True) ∧ (False ∧ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_9
            case inl assump_16 =>
              cases assump_3
              case inl assump_20 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_23
                  case intro assump_26 assump_27 =>
                    cases assump_27
                    case inl assump_30 =>
                      have assump_491 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_39 := assump_4 assump_491
                      apply False.elim assump_39
                    case inr assump_31 =>
                      apply False.elim assump_31
              case inr assump_21 =>
                cases assump_21
                case inl assump_45 =>
                  cases assump_45
                  case inl assump_47 =>
                    cases assump_47
                    case inl assump_49 =>
                      have assump_492 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_56 := assump_4 assump_492
                      apply False.elim assump_56
                    case inr assump_50 =>
                      have assump_493 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_64 := assump_4 assump_493
                      apply False.elim assump_64
                  case inr assump_48 =>
                    cases assump_48
                    case inl assump_68 =>
                      have assump_494 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_75 := assump_4 assump_494
                      apply False.elim assump_75
                    case inr assump_69 =>
                      have assump_495 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_84 := assump_4 assump_495
                      apply False.elim assump_84
                case inr assump_46 =>
                  cases assump_46
                  case intro assump_88 assump_89 =>
                    cases assump_89
                    case intro assump_92 assump_93 =>
                      apply False.elim assump_92
            case inr assump_17 =>
              cases assump_3
              case inl assump_98 =>
                cases assump_98
                case intro assump_100 assump_101 =>
                  cases assump_101
                  case intro assump_104 assump_105 =>
                    cases assump_105
                    case inl assump_108 =>
                      have assump_496 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_118 := assump_4 assump_496
                      apply False.elim assump_118
                    case inr assump_109 =>
                      apply False.elim assump_109
              case inr assump_99 =>
                cases assump_99
                case inl assump_124 =>
                  cases assump_124
                  case inl assump_126 =>
                    cases assump_126
                    case inl assump_128 =>
                      have assump_497 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_135 := assump_4 assump_497
                      apply False.elim assump_135
                    case inr assump_129 =>
                      have assump_498 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_143 := assump_4 assump_498
                      apply False.elim assump_143
                  case inr assump_127 =>
                    cases assump_127
                    case inl assump_147 =>
                      have assump_499 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_155 := assump_4 assump_499
                      apply False.elim assump_155
                    case inr assump_148 =>
                      have assump_500 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_165 := assump_4 assump_500
                      apply False.elim assump_165
                case inr assump_125 =>
                  cases assump_125
                  case intro assump_169 assump_170 =>
                    cases assump_170
                    case intro assump_173 assump_174 =>
                      apply False.elim assump_173
          case inr assump_13 =>
            cases assump_9
            case inl assump_179 =>
              cases assump_3
              case inl assump_183 =>
                cases assump_183
                case intro assump_185 assump_186 =>
                  cases assump_186
                  case intro assump_189 assump_190 =>
                    cases assump_190
                    case inl assump_193 =>
                      have assump_501 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_201 := assump_4 assump_501
                      apply False.elim assump_201
                    case inr assump_194 =>
                      apply False.elim assump_194
              case inr assump_184 =>
                cases assump_184
                case inl assump_207 =>
                  cases assump_207
                  case inl assump_209 =>
                    cases assump_209
                    case inl assump_211 =>
                      have assump_502 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_217 := assump_4 assump_502
                      apply False.elim assump_217
                    case inr assump_212 =>
                      have assump_503 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_224 := assump_4 assump_503
                      apply False.elim assump_224
                  case inr assump_210 =>
                    cases assump_210
                    case inl assump_228 =>
                      have assump_504 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_234 := assump_4 assump_504
                      apply False.elim assump_234
                    case inr assump_229 =>
                      have assump_505 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_242 := assump_4 assump_505
                      apply False.elim assump_242
                case inr assump_208 =>
                  cases assump_208
                  case intro assump_246 assump_247 =>
                    cases assump_247
                    case intro assump_250 assump_251 =>
                      apply False.elim assump_250
            case inr assump_180 =>
              cases assump_3
              case inl assump_256 =>
                cases assump_256
                case intro assump_258 assump_259 =>
                  cases assump_259
                  case intro assump_262 assump_263 =>
                    cases assump_263
                    case inl assump_266 =>
                      have assump_506 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_275 := assump_4 assump_506
                      apply False.elim assump_275
                    case inr assump_267 =>
                      apply False.elim assump_267
              case inr assump_257 =>
                cases assump_257
                case inl assump_281 =>
                  cases assump_281
                  case inl assump_283 =>
                    cases assump_283
                    case inl assump_285 =>
                      have assump_507 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_291 := assump_4 assump_507
                      apply False.elim assump_291
                    case inr assump_286 =>
                      have assump_508 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_298 := assump_4 assump_508
                      apply False.elim assump_298
                  case inr assump_284 =>
                    cases assump_284
                    case inl assump_302 =>
                      have assump_509 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_309 := assump_4 assump_509
                      apply False.elim assump_309
                    case inr assump_303 =>
                      have assump_510 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                      let assump_318 := assump_4 assump_510
                      apply False.elim assump_318
                case inr assump_282 =>
                  cases assump_282
                  case intro assump_322 assump_323 =>
                    cases assump_323
                    case intro assump_326 assump_327 =>
                      apply False.elim assump_326
        case inr assump_11 =>
          cases assump_9
          case inl assump_332 =>
            cases assump_3
            case inl assump_336 =>
              cases assump_336
              case intro assump_338 assump_339 =>
                cases assump_339
                case intro assump_342 assump_343 =>
                  cases assump_343
                  case inl assump_346 =>
                    have assump_511 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_355 := assump_4 assump_511
                    apply False.elim assump_355
                  case inr assump_347 =>
                    apply False.elim assump_347
            case inr assump_337 =>
              cases assump_337
              case inl assump_361 =>
                cases assump_361
                case inl assump_363 =>
                  cases assump_363
                  case inl assump_365 =>
                    have assump_512 : p6 := by
                      exact assump_365
                    let assump_371 := assump_11 assump_512
                    apply False.elim assump_371
                  case inr assump_366 =>
                    have assump_513 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_379 := assump_4 assump_513
                    apply False.elim assump_379
                case inr assump_364 =>
                  cases assump_364
                  case inl assump_383 =>
                    have assump_514 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_390 := assump_4 assump_514
                    apply False.elim assump_390
                  case inr assump_384 =>
                    have assump_515 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_399 := assump_4 assump_515
                    apply False.elim assump_399
              case inr assump_362 =>
                cases assump_362
                case intro assump_403 assump_404 =>
                  cases assump_404
                  case intro assump_407 assump_408 =>
                    apply False.elim assump_407
          case inr assump_333 =>
            cases assump_3
            case inl assump_413 =>
              cases assump_413
              case intro assump_415 assump_416 =>
                cases assump_416
                case intro assump_419 assump_420 =>
                  cases assump_420
                  case inl assump_423 =>
                    have assump_516 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_433 := assump_4 assump_516
                    apply False.elim assump_433
                  case inr assump_424 =>
                    apply False.elim assump_424
            case inr assump_414 =>
              cases assump_414
              case inl assump_439 =>
                cases assump_439
                case inl assump_441 =>
                  cases assump_441
                  case inl assump_443 =>
                    have assump_517 : p6 := by
                      exact assump_443
                    let assump_449 := assump_11 assump_517
                    apply False.elim assump_449
                  case inr assump_444 =>
                    have assump_518 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_457 := assump_4 assump_518
                    apply False.elim assump_457
                case inr assump_442 =>
                  cases assump_442
                  case inl assump_461 =>
                    have assump_519 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_469 := assump_4 assump_519
                    apply False.elim assump_469
                  case inr assump_462 =>
                    have assump_520 : ((p1 ∨ True) ∨ (p4 ∧ p4)) := by
                      apply Or.inl
                      apply Or.inr
                      apply True.intro
                    let assump_479 := assump_4 assump_520
                    apply False.elim assump_479
              case inr assump_440 =>
                cases assump_440
                case intro assump_483 assump_484 =>
                  cases assump_484
                  case intro assump_487 assump_488 =>
                    apply False.elim assump_487


variable (p2 p7 p4 p6 p5 p3 p1 p0 : Prop)
theorem file66_39389 : (((((p6 ∧ p2) ∨ (False → p4)) ∧ ((False ∨ p1) ∨ (True ∨ False))) ∨ (((p1 → False) ∧ (p5 → False)) ∧ ((p5 ∨ p3) → False))) ∨ ((((p7 → False) → False) ∨ ((p3 ∧ p2) → (False ∧ p5))) → (((p2 ∧ p4) ∨ (p0 ∨ p2)) ∨ ((p2 → p1) ∨ (p3 ∨ p5))))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inr
  intro assump_1
  apply False.elim assump_1
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p2 p7 p6 p4 p0 p5 p1 p3 : Prop)
theorem file66_39853 : (((((False → False) → False) → ((p4 → False) → (False → False))) ∧ (((p2 → p6) → (p1 ∨ False)) ∧ ((p3 → p1) → (p1 ∧ p4)))) → ((((p5 ∧ p0) ∨ (False ∧ p1)) → ((p5 → False) → False)) → (((p7 → p2) → (p7 → p2)) ∨ ((True ∧ p5) ∧ (p7 → False))))) := by
  intro assump_47
  intro assump_48
  cases assump_47
  case intro assump_51 assump_52 =>
    cases assump_52
    case intro assump_55 assump_56 =>
      apply Or.inl
      intro assump_61
      intro assump_62
      have assump_69 : p7 := by
        exact assump_62
      let assump_67 := assump_61 assump_69
      exact assump_67


variable (p1 p5 p6 p2 p3 p7 : Prop)
theorem file66_40492 : ((((((p1 → False) ∧ (p7 → p5)) → ((p7 → False) → (p6 → True))) → (((p3 → False) ∧ (p6 → False)) → ((False ∧ p2) → (p5 → p5)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 → False) ∧ (p7 → p5)) → ((p7 → False) → (p6 → True))) → (((p3 → False) ∧ (p6 → False)) → ((False ∧ p2) → (p5 → p5)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p6 p1 p7 p2 p5 p4 p3 : Prop)
theorem file66_41107 : ((((((p6 ∧ False) → False) → False) ∧ (((False ∨ p4) ∧ (p6 → False)) → ((p3 → False) ∨ (p2 ∧ p3)))) ∨ ((((True ∧ p5) → (True ∧ p6)) ∧ ((p0 ∨ False) ∧ (p2 ∧ p0))) ∧ (((p2 ∨ True) ∨ (p1 ∨ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_48 : ((p6 ∧ False) → False) := by
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
      let assump_11 := assump_4 assump_48
      apply False.elim assump_11
  case inr assump_3 =>
    cases assump_3
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          cases assump_28
          case inl assump_30 =>
            cases assump_29
            case intro assump_34 assump_35 =>
              have assump_49 : ((p2 ∨ True) ∨ (p1 ∨ p7)) := by
                apply Or.inl
                apply Or.inl
                exact assump_34
              let assump_42 := assump_23 assump_49
              apply False.elim assump_42
          case inr assump_31 =>
            apply False.elim assump_31


variable (p6 p5 p2 p0 p3 p4 : Prop)
theorem file66_42406 : (((((p0 ∧ False) ∧ (p2 ∧ True)) ∧ ((p4 ∧ p5) ∨ (p0 ∧ p3))) → False) ∨ ((((p3 → False) → False) → ((p6 → False) → (p2 ∨ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7


variable (p4 p1 p2 p5 p6 p3 p0 : Prop)
theorem file66_42841 : (((((p0 → p0) → (p1 → False)) ∧ ((p6 ∧ p5) ∨ (p4 ∨ p0))) ∧ (((p3 ∧ p2) ∧ (p5 ∨ False)) ∧ ((p6 → False) → False))) → ((((p0 ∨ True) → (p0 ∧ p0)) ∧ ((p2 ∧ True) ∧ (p6 ∧ p1))) → (((True ∧ p3) ∧ (p2 ∧ p1)) ∧ ((p1 ∨ p1) ∧ (p5 → p3))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  apply And.intro
  apply True.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          cases assump_1
          case intro assump_21 assump_22 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              cases assump_24
              case inl assump_27 =>
                cases assump_27
                case intro assump_29 assump_30 =>
                  cases assump_22
                  case intro assump_35 assump_36 =>
                    cases assump_35
                    case intro assump_37 assump_38 =>
                      cases assump_37
                      case intro assump_39 assump_40 =>
                        cases assump_38
                        case inl assump_45 =>
                          exact assump_39
                        case inr assump_46 =>
                          apply False.elim assump_46
              case inr assump_28 =>
                cases assump_28
                case inl assump_53 =>
                  cases assump_22
                  case intro assump_57 assump_58 =>
                    cases assump_57
                    case intro assump_59 assump_60 =>
                      cases assump_59
                      case intro assump_61 assump_62 =>
                        cases assump_60
                        case inl assump_67 =>
                          exact assump_61
                        case inr assump_68 =>
                          apply False.elim assump_68
                case inr assump_54 =>
                  cases assump_22
                  case intro assump_77 assump_78 =>
                    cases assump_77
                    case intro assump_79 assump_80 =>
                      cases assump_79
                      case intro assump_81 assump_82 =>
                        cases assump_80
                        case inl assump_87 =>
                          exact assump_81
                        case inr assump_88 =>
                          apply False.elim assump_88
  apply And.intro
  cases assump_2
  case intro assump_95 assump_96 =>
    cases assump_96
    case intro assump_99 assump_100 =>
      cases assump_99
      case intro assump_101 assump_102 =>
        cases assump_100
        case intro assump_107 assump_108 =>
          cases assump_1
          case intro assump_113 assump_114 =>
            cases assump_113
            case intro assump_115 assump_116 =>
              cases assump_116
              case inl assump_119 =>
                cases assump_119
                case intro assump_121 assump_122 =>
                  cases assump_114
                  case intro assump_127 assump_128 =>
                    cases assump_127
                    case intro assump_129 assump_130 =>
                      cases assump_129
                      case intro assump_131 assump_132 =>
                        cases assump_130
                        case inl assump_137 =>
                          exact assump_132
                        case inr assump_138 =>
                          apply False.elim assump_138
              case inr assump_120 =>
                cases assump_120
                case inl assump_145 =>
                  cases assump_114
                  case intro assump_149 assump_150 =>
                    cases assump_149
                    case intro assump_151 assump_152 =>
                      cases assump_151
                      case intro assump_153 assump_154 =>
                        cases assump_152
                        case inl assump_159 =>
                          exact assump_154
                        case inr assump_160 =>
                          apply False.elim assump_160
                case inr assump_146 =>
                  cases assump_114
                  case intro assump_169 assump_170 =>
                    cases assump_169
                    case intro assump_171 assump_172 =>
                      cases assump_171
                      case intro assump_173 assump_174 =>
                        cases assump_172
                        case inl assump_179 =>
                          exact assump_174
                        case inr assump_180 =>
                          apply False.elim assump_180
  cases assump_2
  case intro assump_187 assump_188 =>
    cases assump_188
    case intro assump_191 assump_192 =>
      cases assump_191
      case intro assump_193 assump_194 =>
        cases assump_192
        case intro assump_199 assump_200 =>
          cases assump_1
          case intro assump_205 assump_206 =>
            cases assump_205
            case intro assump_207 assump_208 =>
              cases assump_208
              case inl assump_211 =>
                cases assump_211
                case intro assump_213 assump_214 =>
                  cases assump_206
                  case intro assump_219 assump_220 =>
                    cases assump_219
                    case intro assump_221 assump_222 =>
                      cases assump_221
                      case intro assump_223 assump_224 =>
                        cases assump_222
                        case inl assump_229 =>
                          exact assump_200
                        case inr assump_230 =>
                          apply False.elim assump_230
              case inr assump_212 =>
                cases assump_212
                case inl assump_237 =>
                  cases assump_206
                  case intro assump_241 assump_242 =>
                    cases assump_241
                    case intro assump_243 assump_244 =>
                      cases assump_243
                      case intro assump_245 assump_246 =>
                        cases assump_244
                        case inl assump_251 =>
                          exact assump_200
                        case inr assump_252 =>
                          apply False.elim assump_252
                case inr assump_238 =>
                  cases assump_206
                  case intro assump_261 assump_262 =>
                    cases assump_261
                    case intro assump_263 assump_264 =>
                      cases assump_263
                      case intro assump_265 assump_266 =>
                        cases assump_264
                        case inl assump_271 =>
                          exact assump_200
                        case inr assump_272 =>
                          apply False.elim assump_272
  apply And.intro
  cases assump_2
  case intro assump_279 assump_280 =>
    cases assump_280
    case intro assump_283 assump_284 =>
      cases assump_283
      case intro assump_285 assump_286 =>
        cases assump_284
        case intro assump_291 assump_292 =>
          cases assump_1
          case intro assump_297 assump_298 =>
            cases assump_297
            case intro assump_299 assump_300 =>
              cases assump_300
              case inl assump_303 =>
                cases assump_303
                case intro assump_305 assump_306 =>
                  cases assump_298
                  case intro assump_311 assump_312 =>
                    cases assump_311
                    case intro assump_313 assump_314 =>
                      cases assump_313
                      case intro assump_315 assump_316 =>
                        cases assump_314
                        case inl assump_321 =>
                          apply Or.inl
                          exact assump_292
                        case inr assump_322 =>
                          apply False.elim assump_322
              case inr assump_304 =>
                cases assump_304
                case inl assump_329 =>
                  cases assump_298
                  case intro assump_333 assump_334 =>
                    cases assump_333
                    case intro assump_335 assump_336 =>
                      cases assump_335
                      case intro assump_337 assump_338 =>
                        cases assump_336
                        case inl assump_343 =>
                          apply Or.inl
                          exact assump_292
                        case inr assump_344 =>
                          apply False.elim assump_344
                case inr assump_330 =>
                  cases assump_298
                  case intro assump_353 assump_354 =>
                    cases assump_353
                    case intro assump_355 assump_356 =>
                      cases assump_355
                      case intro assump_357 assump_358 =>
                        cases assump_356
                        case inl assump_363 =>
                          apply Or.inl
                          exact assump_292
                        case inr assump_364 =>
                          apply False.elim assump_364
  intro assump_371
  cases assump_2
  case intro assump_374 assump_375 =>
    cases assump_375
    case intro assump_378 assump_379 =>
      cases assump_378
      case intro assump_380 assump_381 =>
        cases assump_379
        case intro assump_386 assump_387 =>
          cases assump_1
          case intro assump_392 assump_393 =>
            cases assump_392
            case intro assump_394 assump_395 =>
              cases assump_395
              case inl assump_398 =>
                cases assump_398
                case intro assump_400 assump_401 =>
                  cases assump_393
                  case intro assump_406 assump_407 =>
                    cases assump_406
                    case intro assump_408 assump_409 =>
                      cases assump_408
                      case intro assump_410 assump_411 =>
                        cases assump_409
                        case inl assump_416 =>
                          exact assump_410
                        case inr assump_417 =>
                          apply False.elim assump_417
              case inr assump_399 =>
                cases assump_399
                case inl assump_424 =>
                  cases assump_393
                  case intro assump_428 assump_429 =>
                    cases assump_428
                    case intro assump_430 assump_431 =>
                      cases assump_430
                      case intro assump_432 assump_433 =>
                        cases assump_431
                        case inl assump_438 =>
                          exact assump_432
                        case inr assump_439 =>
                          apply False.elim assump_439
                case inr assump_425 =>
                  cases assump_393
                  case intro assump_448 assump_449 =>
                    cases assump_448
                    case intro assump_450 assump_451 =>
                      cases assump_450
                      case intro assump_452 assump_453 =>
                        cases assump_451
                        case inl assump_458 =>
                          exact assump_452
                        case inr assump_459 =>
                          apply False.elim assump_459


variable (p2 p3 p5 p4 p7 p6 p1 p0 : Prop)
theorem file66_54503 : (((((p1 → False) ∧ (p1 ∧ False)) → ((False ∨ p3) ∨ (True → False))) ∨ (((p3 ∧ p2) → False) ∧ ((p5 → p3) ∧ (p7 ∧ p0)))) ∨ ((((False → False) → (p6 → p2)) ∨ ((p0 ∨ p7) ∧ (p7 → False))) ∧ (((p2 ∨ False) ∧ (p3 → False)) ∨ ((False → p6) ∧ (p3 → p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p7 p4 p2 p1 : Prop)
theorem file66_54996 : ((((((True ∧ False) → False) → False) → (((p4 ∧ p4) → False) ∧ ((p7 → p2) → (p4 → p1)))) → False) → False) := by
  intro assump_1
  have assump_48 : ((((True ∧ False) → False) → False) → (((p4 ∧ p4) → False) ∧ ((p7 → p2) → (p4 → p1)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_49 : ((True ∧ False) → False) := by
        intro assump_16
        cases assump_16
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
      let assump_15 := assump_5 assump_49
      apply False.elim assump_15
    intro assump_26
    intro assump_27
    have assump_50 : ((True ∧ False) → False) := by
      intro assump_35
      cases assump_35
      case intro assump_36 assump_37 =>
        apply False.elim assump_37
    let assump_34 := assump_5 assump_50
    apply False.elim assump_34
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p4 p7 p0 p5 p3 p1 : Prop)
theorem file66_56014 : ((((((p4 ∧ p1) ∨ (p0 ∧ p0)) ∧ ((p1 → False) → (p1 → p0))) → False) ∧ ((((p3 ∨ p5) → False) ∨ ((p4 → p3) → False)) ∧ (((p7 → False) → (True ∨ True)) → False))) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_20
    case intro assump_23 assump_24 =>
      cases assump_23
      case inl assump_25 =>
        have assump_49 : ((p7 → False) → (True ∨ True)) := by
          intro assump_32
          apply Or.inl
          apply True.intro
        let assump_31 := assump_24 assump_49
        apply False.elim assump_31
      case inr assump_26 =>
        have assump_50 : ((p7 → False) → (True ∨ True)) := by
          intro assump_43
          apply Or.inl
          apply True.intro
        let assump_42 := assump_24 assump_50
        apply False.elim assump_42


variable (p6 p1 p3 p4 p5 : Prop)
theorem file66_56889 : (((((p5 → False) → (p3 → False)) → ((p6 → p6) ∧ (False → p4))) → (((p5 ∨ p1) → (True ∨ False)) → False)) → False) := by
  intro assump_1
  have assump_25 : (((p5 → False) → (p3 → False)) → ((p6 → p6) ∧ (False → p4))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    exact assump_6
    intro assump_11
    apply False.elim assump_11
  let assump_4 := assump_1 assump_25
  have assump_26 : ((p5 ∨ p1) → (True ∨ False)) := by
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      apply Or.inl
      apply True.intro
    case inr assump_17 =>
      apply Or.inl
      apply True.intro
  let assump_14 := assump_4 assump_26
  apply False.elim assump_14


variable (p4 p7 p3 : Prop)
theorem file66_57625 : ((((((p7 → False) ∨ (p4 → False)) ∧ ((p3 → True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p7 → False) ∨ (p4 → False)) ∧ ((p3 → True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_32 : (p3 → True) := by
          intro assump_15
          apply True.intro
        let assump_14 := assump_7 assump_32
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_33 : (p3 → True) := by
          intro assump_24
          apply True.intro
        let assump_23 := assump_7 assump_33
        apply False.elim assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p1 p6 p5 p7 p4 p0 : Prop)
theorem file66_58449 : (((((p5 ∨ p7) ∨ (p4 ∨ True)) → False) → (((p7 → p5) ∨ (p4 ∨ p0)) → False)) → ((((True ∧ p1) ∨ (p6 → False)) ∧ ((True ∧ False) ∨ (False ∧ p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            apply False.elim assump_16
        case inr assump_14 =>
          cases assump_14
          case intro assump_21 assump_22 =>
            apply False.elim assump_21
    case inr assump_6 =>
      cases assump_4
      case inl assump_27 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          apply False.elim assump_30
      case inr assump_28 =>
        cases assump_28
        case intro assump_35 assump_36 =>
          apply False.elim assump_35


variable (p3 p4 p0 p1 p7 p6 : Prop)
theorem file66_59465 : (((((p3 ∧ p7) → (p7 → False)) → False) ∧ (((p6 ∧ False) ∨ (False → p1)) → False)) → ((((False ∨ p7) → False) → ((p6 ∧ False) → (p7 ∧ p4))) ∧ (((p1 → False) ∨ (p0 ∧ False)) → ((p6 → p4) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_5
  cases assump_3
  case intro assump_10 assump_11 =>
    apply False.elim assump_11
  intro assump_16
  intro assump_17
  cases assump_16
  case inl assump_20 =>
    cases assump_1
    case intro assump_24 assump_25 =>
      have assump_43 : ((p6 ∧ False) ∨ (False → p1)) := by
        apply Or.inr
        intro assump_31
        apply False.elim assump_31
      let assump_30 := assump_25 assump_43
      apply False.elim assump_30
  case inr assump_21 =>
    cases assump_21
    case intro assump_37 assump_38 =>
      apply False.elim assump_38


variable (p4 p0 p1 : Prop)
theorem file66_60436 : ((((((p1 ∧ False) → (p4 ∧ p0)) → False) → False) → False) → False) := by
  intro assump_10
  have assump_37 : ((((p1 ∧ False) → (p4 ∧ p0)) → False) → False) := by
    intro assump_14
    have assump_38 : ((p1 ∧ False) → (p4 ∧ p0)) := by
      intro assump_18
      apply And.intro
      cases assump_18
      case intro assump_19 assump_20 =>
        apply False.elim assump_20
      cases assump_18
      case intro assump_25 assump_26 =>
        apply False.elim assump_26
    let assump_17 := assump_14 assump_38
    apply False.elim assump_17
  let assump_13 := assump_10 assump_37
  apply False.elim assump_13


variable (p0 p4 p5 p3 p2 : Prop)
theorem file66_61108 : ((((((True ∧ p4) ∧ (True → False)) → ((False → False) ∧ (p4 → False))) → False) ∨ ((((p2 → False) → False) → False) ∧ (((p5 → p3) ∨ (p5 ∧ p0)) ∧ ((p0 → p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_65 : (((True ∧ p4) ∧ (True → False)) → ((False → False) ∧ (p4 → False))) := by
      intro assump_7
      apply And.intro
      intro assump_8
      apply False.elim assump_8
      intro assump_11
      cases assump_7
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          have assump_66 : True := by
            apply True.intro
          let assump_24 := assump_15 assump_66
          apply False.elim assump_24
    let assump_6 := assump_2 assump_65
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_31 assump_32 =>
      cases assump_32
      case intro assump_35 assump_36 =>
        cases assump_35
        case inl assump_37 =>
          have assump_67 : (p0 → p0) := by
            intro assump_44
            exact assump_44
          let assump_43 := assump_36 assump_67
          apply False.elim assump_43
        case inr assump_38 =>
          cases assump_38
          case intro assump_50 assump_51 =>
            have assump_68 : (p0 → p0) := by
              intro assump_59
              exact assump_59
            let assump_58 := assump_36 assump_68
            apply False.elim assump_58


variable (p0 p1 : Prop)
theorem file66_62628 : (((((p1 ∧ p1) → False) → ((p0 → False) → (True ∨ p1))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p1 ∧ p1) → False) → ((p0 → False) → (True ∨ p1))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p4 p3 p2 p6 p5 : Prop)
theorem file66_63000 : (((((False ∨ p5) → False) ∧ ((False → p3) → False)) ∧ (((p2 → p4) ∧ (p2 → True)) ∧ ((p5 ∨ p6) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_30 : (False → p3) := by
            intro assump_24
            apply False.elim assump_24
          let assump_23 := assump_5 assump_30
          apply False.elim assump_23


variable (p1 p6 p2 p4 p3 p5 p0 p7 : Prop)
theorem file66_63632 : (((((p7 → False) ∧ (p4 ∧ False)) → ((True ∨ p6) → False)) ∨ (((True ∨ False) ∨ (p5 → p7)) ∧ ((False ∧ p0) ∧ (p1 ∨ False)))) ∨ ((((p6 ∨ p7) → False) → ((p0 ∨ p3) → (p6 ∧ p2))) ∨ (((p1 ∧ p5) ∧ (p2 ∨ p3)) → ((p5 → False) ∨ (p0 ∨ p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  case inr assump_4 =>
    cases assump_1
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        apply False.elim assump_24


variable (p5 p7 p1 p3 : Prop)
theorem file66_64358 : ((((((p1 ∧ False) ∧ (False → False)) → ((p3 → False) ∨ (p5 ∧ True))) ∨ (((False → p7) → False) → False)) → False) → False) := by
  intro assump_14
  have assump_30 : ((((p1 ∧ False) ∧ (False → False)) → ((p3 → False) ∨ (p5 ∧ True))) ∨ (((False → p7) → False) → False)) := by
    apply Or.inl
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        apply False.elim assump_22
  let assump_17 := assump_14 assump_30
  apply False.elim assump_17


variable (p0 p2 p7 p5 p6 p1 : Prop)
theorem file66_64953 : (((((p7 ∧ p6) → (p5 → False)) ∧ ((p7 ∨ True) → False)) → False) ∨ ((((p1 → False) ∨ (False ∧ True)) ∧ ((p7 → p1) → (p2 → p6))) → (((p0 ∨ p6) ∧ (p2 ∨ p6)) ∧ ((p6 ∧ p1) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p0 p4 p6 p1 p3 p2 : Prop)
theorem file66_65438 : (((((p3 ∧ p4) ∨ (p1 ∧ True)) ∧ ((p3 ∨ True) → False)) → (((p4 ∧ p2) → False) → False)) ∨ ((((p6 ∧ p1) ∨ (p0 → True)) → ((p4 → p6) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_33 : (p3 ∨ True) := by
          apply Or.inl
          exact assump_9
        let assump_17 := assump_6 assump_33
        apply False.elim assump_17
    case inr assump_8 =>
      cases assump_8
      case intro assump_21 assump_22 =>
        have assump_34 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_29 := assump_6 assump_34
        apply False.elim assump_29


variable (p6 p0 p1 p7 p4 p2 : Prop)
theorem file66_66286 : (((((p7 → False) → (p0 → False)) ∨ ((p4 ∨ p7) ∨ (True ∧ p4))) → False) → ((((False ∨ p4) ∧ (p4 ∧ p2)) → ((p1 ∧ p6) ∨ (True ∨ p1))) ∨ (((True ∧ p6) ∨ (p2 → p7)) ∧ ((True → False) ∨ (p4 → False))))) := by
  intro assump_28
  apply Or.inl
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    cases assump_32
    case inl assump_34 =>
      apply False.elim assump_34
    case inr assump_35 =>
      cases assump_33
      case intro assump_40 assump_41 =>
        apply Or.inr
        apply Or.inl
        apply True.intro


variable (p1 p5 p4 p0 p6 : Prop)
theorem file66_66885 : (((((p6 → p0) → (False → p5)) → False) → False) ∨ ((((p5 ∧ True) ∧ (p4 → p4)) ∧ ((p0 ∨ p5) → False)) ∧ (((True ∧ p1) ∧ (p5 ∨ p1)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p6 → p0) → (False → p5)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p7 p0 p3 : Prop)
theorem file66_67303 : (((((p3 ∨ p7) ∨ (p3 → False)) ∨ ((p0 ∧ p5) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((p3 ∨ p7) ∨ (p3 → False)) ∨ ((p0 ∧ p5) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : (((p3 ∨ p7) ∨ (p3 → False)) ∨ ((p0 ∧ p5) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p4 p3 p6 p0 p2 : Prop)
theorem file66_67873 : ((((((p0 ∧ p6) → False) ∨ ((True ∧ p0) → False)) → (((p3 ∧ p0) ∧ (p2 → p4)) ∨ ((p2 → False) → (False → p0)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p0 ∧ p6) → False) ∨ ((True ∧ p0) → False)) → (((p3 ∧ p0) ∧ (p2 → p4)) ∨ ((p2 → False) → (False → p0)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    case inr assump_7 =>
      apply Or.inr
      intro assump_16
      intro assump_17
      apply False.elim assump_17
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p6 p3 p7 p5 p4 p1 p0 : Prop)
theorem file66_68565 : (((((p5 → p5) ∧ (False ∧ False)) ∧ ((p0 ∧ p1) → False)) ∧ (((p1 ∧ False) → False) ∨ ((False → p5) → (p1 → False)))) → ((((p0 → False) ∧ (p4 ∧ False)) ∨ ((p4 ∨ True) → False)) ∧ (((False → p3) ∨ (p6 ∨ p7)) → ((p1 ∨ p3) ∨ (p0 ∨ False))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    cases assump_1
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          cases assump_24
          case intro assump_27 assump_28 =>
            apply False.elim assump_27
  case inr assump_16 =>
    cases assump_16
    case inl assump_31 =>
      cases assump_1
      case intro assump_35 assump_36 =>
        cases assump_35
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            cases assump_40
            case intro assump_43 assump_44 =>
              apply False.elim assump_43
    case inr assump_32 =>
      cases assump_1
      case intro assump_49 assump_50 =>
        cases assump_49
        case intro assump_51 assump_52 =>
          cases assump_51
          case intro assump_53 assump_54 =>
            cases assump_54
            case intro assump_57 assump_58 =>
              apply False.elim assump_57


variable (p1 p4 p3 p0 p7 p6 p5 : Prop)
theorem file66_70247 : (((((p7 ∧ p3) ∨ (False ∧ True)) → ((p0 ∧ p3) ∧ (p6 → False))) → False) → ((((p6 ∧ p3) ∨ (p3 ∨ p4)) → False) → (((p7 ∧ False) ∧ (p5 → False)) → ((p1 → False) → (False → p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p0 p2 p6 p4 : Prop)
theorem file66_70596 : (((((False → False) ∨ (p4 → False)) → False) → False) ∨ ((((p6 → False) → (p2 → p0)) → False) → False)) := by
  apply Or.inl
  intro assump_5
  have assump_15 : ((False → False) ∨ (p4 → False)) := by
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p5 p1 p4 p0 p2 p6 p7 : Prop)
theorem file66_70990 : (((((p6 ∨ p2) ∨ (p0 → False)) ∧ ((p6 ∨ p7) → (p6 → p0))) ∧ (((p4 ∧ p5) ∨ (p0 → False)) ∧ ((False ∧ p2) ∧ (True ∨ p1)))) → False) := by
  intro assump_32
  cases assump_32
  case intro assump_33 assump_34 =>
    cases assump_33
    case intro assump_35 assump_36 =>
      cases assump_35
      case inl assump_37 =>
        cases assump_37
        case inl assump_39 =>
          cases assump_34
          case intro assump_45 assump_46 =>
            cases assump_45
            case inl assump_47 =>
              cases assump_47
              case intro assump_49 assump_50 =>
                cases assump_46
                case intro assump_55 assump_56 =>
                  cases assump_55
                  case intro assump_57 assump_58 =>
                    apply False.elim assump_57
            case inr assump_48 =>
              cases assump_46
              case intro assump_63 assump_64 =>
                cases assump_63
                case intro assump_65 assump_66 =>
                  apply False.elim assump_65
        case inr assump_40 =>
          cases assump_34
          case intro assump_73 assump_74 =>
            cases assump_73
            case inl assump_75 =>
              cases assump_75
              case intro assump_77 assump_78 =>
                cases assump_74
                case intro assump_83 assump_84 =>
                  cases assump_83
                  case intro assump_85 assump_86 =>
                    apply False.elim assump_85
            case inr assump_76 =>
              cases assump_74
              case intro assump_91 assump_92 =>
                cases assump_91
                case intro assump_93 assump_94 =>
                  apply False.elim assump_93
      case inr assump_38 =>
        cases assump_34
        case intro assump_101 assump_102 =>
          cases assump_101
          case inl assump_103 =>
            cases assump_103
            case intro assump_105 assump_106 =>
              cases assump_102
              case intro assump_111 assump_112 =>
                cases assump_111
                case intro assump_113 assump_114 =>
                  apply False.elim assump_113
          case inr assump_104 =>
            cases assump_102
            case intro assump_119 assump_120 =>
              cases assump_119
              case intro assump_121 assump_122 =>
                apply False.elim assump_121


variable (p3 p7 p4 p5 p2 p1 p6 p0 : Prop)
theorem file66_73463 : (((((p0 → p4) ∧ (True → False)) → ((p2 ∧ p3) → (p5 → p3))) ∨ (((p1 ∧ p1) ∨ (False ∧ p0)) → False)) ∨ ((((p1 → p1) ∧ (p1 → False)) ∨ ((p2 ∨ p5) → False)) ∧ (((p0 ∧ p2) ∧ (True ∧ p7)) ∨ ((p6 ∨ p7) ∨ (p6 → p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      exact assump_7


variable (p5 p3 p7 p4 p6 p0 : Prop)
theorem file66_73950 : ((((((p0 ∧ False) ∧ (p4 ∧ p5)) → ((p6 → False) ∧ (p4 ∨ p7))) ∨ (((p0 → p7) ∨ (True → p3)) ∨ ((p7 → False) ∧ (p3 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p0 ∧ False) ∧ (p4 ∧ p5)) → ((p6 → False) ∧ (p4 ∨ p7))) ∨ (((p0 → p7) ∨ (True → p3)) ∨ ((p7 → False) ∧ (p3 ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    cases assump_5
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        apply False.elim assump_20
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p4 p3 p1 p7 p5 p0 : Prop)
theorem file66_74762 : (((((p5 ∧ p7) ∧ (p0 ∨ p3)) → ((p4 ∧ p1) ∨ (False → p1))) ∨ (((True ∧ p7) ∨ (False → p3)) → False)) ∧ ((((p4 ∨ p1) → False) ∧ ((True ∨ p1) → False)) → False)) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        apply Or.inr
        intro assump_14
        apply False.elim assump_14
      case inr assump_11 =>
        apply Or.inr
        intro assump_19
        apply False.elim assump_19
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    have assump_33 : (True ∨ p1) := by
      apply Or.inl
      apply True.intro
    let assump_29 := assump_24 assump_33
    apply False.elim assump_29


variable (p3 p0 p7 p6 p4 p5 p1 p2 : Prop)
theorem file66_75610 : (((((p5 ∧ True) ∧ (p4 ∧ False)) → ((p5 ∧ p4) → False)) ∨ (((p1 → p1) → (p5 ∨ False)) → ((p3 → False) ∧ (p1 ∨ p1)))) ∨ ((((True ∧ p7) ∧ (p3 ∨ p5)) ∨ ((p2 ∧ p2) ∧ (p7 ∧ p2))) → (((p7 ∧ p6) ∨ (p0 → False)) ∨ ((p5 → p2) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_92
  intro assump_93
  cases assump_93
  case intro assump_94 assump_95 =>
    cases assump_92
    case intro assump_100 assump_101 =>
      cases assump_100
      case intro assump_102 assump_103 =>
        cases assump_101
        case intro assump_108 assump_109 =>
          apply False.elim assump_109


variable (p2 p7 p3 p1 p6 : Prop)
theorem file66_76253 : (((((p3 ∧ p1) ∨ (p1 ∨ True)) → False) ∧ (((True → p1) → False) ∧ ((False ∧ p6) ∧ (p7 ∧ p2)))) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_13
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          apply False.elim assump_22


variable (p6 p2 p0 p7 p5 p3 : Prop)
theorem file66_76717 : (((((p5 → False) ∨ (p7 ∨ p7)) → False) ∨ (((p7 → False) ∨ (False ∨ True)) → False)) → ((((True ∨ False) → False) ∧ ((p7 ∨ p6) → (p3 ∧ p0))) → (((False ∧ p3) ∧ (p2 ∨ False)) → False))) := by
  intro assump_9
  intro assump_10
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      apply False.elim assump_14


variable (p5 p2 p3 p4 : Prop)
theorem file66_77159 : (((((True → False) ∧ (p3 ∧ p5)) → ((p4 ∨ p2) → False)) → False) → False) := by
  intro assump_1
  have assump_48 : (((True → False) ∧ (p3 ∧ p5)) → ((p4 ∨ p2) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          have assump_49 : True := by
            apply True.intro
          let assump_23 := assump_11 assump_49
          apply False.elim assump_23
    case inr assump_8 =>
      cases assump_5
      case intro assump_29 assump_30 =>
        cases assump_30
        case intro assump_33 assump_34 =>
          have assump_50 : True := by
            apply True.intro
          let assump_41 := assump_29 assump_50
          apply False.elim assump_41
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p1 p2 p3 : Prop)
theorem file66_78112 : ((((((True → p1) ∧ (p3 ∧ False)) → False) ∨ (((True → False) ∧ (p2 ∧ p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_19 : ((((True → p1) ∧ (p3 ∧ False)) → False) ∨ (((True → False) ∧ (p2 ∧ p3)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p0 p2 p3 : Prop)
theorem file66_78650 : ((((((p4 → p0) → False) → False) → (((False ∧ False) ∧ (True ∧ p3)) → ((p3 ∧ False) ∧ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p4 → p0) → False) → False) → (((False ∧ False) ∧ (True ∧ p3)) → ((p3 ∧ False) ∧ (p2 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    cases assump_6
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
    intro assump_19
    cases assump_6
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p5 p3 p2 p7 : Prop)
theorem file66_79592 : (((((False → False) → (False ∧ p7)) → ((True ∨ p5) → (True ∨ p2))) ∧ (((p5 ∧ False) ∨ (p3 → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((p5 ∧ False) ∨ (p3 → True)) := by
      apply Or.inr
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p6 p3 p0 p7 p1 p5 p4 : Prop)
theorem file66_80035 : (((((p5 → p6) → (True ∨ p5)) ∧ ((True ∨ p4) → False)) → (((p7 → p1) → False) ∧ ((p1 ∧ p3) ∨ (p7 ∨ False)))) ∨ ((((True ∨ p1) → False) ∨ ((p7 → False) ∧ (p6 → p7))) ∨ (((p4 → True) → False) ∧ ((p7 ∧ p3) ∧ (p0 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_25 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_11 := assump_6 assump_25
    apply False.elim assump_11
  cases assump_1
  case intro assump_15 assump_16 =>
    have assump_26 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_21 := assump_16 assump_26
    apply False.elim assump_21


variable (p7 p3 p4 p0 p2 p1 p6 : Prop)
theorem file66_80801 : (((((p4 ∧ p4) ∧ (p7 ∧ p0)) → False) ∧ (((True → p1) ∧ (True ∧ True)) ∧ ((p6 ∧ p1) ∧ (p6 → False)))) → ((((p3 ∨ p1) → (p4 ∧ p0)) → False) ∨ (((p6 → False) ∨ (p3 → p0)) ∨ ((p7 → p2) ∧ (p3 ∨ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply Or.inl
              intro assump_28
              have assump_39 : p6 := by
                exact assump_20
              let assump_35 := assump_19 assump_39
              apply False.elim assump_35


variable (p7 p1 p6 p3 p5 p0 p2 p4 : Prop)
theorem file66_81680 : (((((False → False) → False) ∧ ((p0 → p7) ∧ (p5 → False))) ∧ (((True ∨ p3) ∨ (p7 ∨ p1)) ∧ ((p7 → False) ∧ (p0 ∧ p2)))) → ((((p6 → True) → (True → False)) → False) ∨ (((p5 ∨ p7) ∨ (p4 → False)) → ((p6 ∧ p7) → (p6 → p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_15
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  apply Or.inl
                  intro assump_32
                  have assump_106 : (p6 → True) := by
                    intro assump_36
                    apply True.intro
                  let assump_35 := assump_32 assump_106
                  have assump_107 : True := by
                    apply True.intro
                  let assump_37 := assump_35 assump_107
                  apply False.elim assump_37
            case inr assump_19 =>
              cases assump_15
              case intro assump_43 assump_44 =>
                cases assump_44
                case intro assump_47 assump_48 =>
                  apply Or.inl
                  intro assump_53
                  have assump_108 : (p6 → True) := by
                    intro assump_57
                    apply True.intro
                  let assump_56 := assump_53 assump_108
                  have assump_109 : True := by
                    apply True.intro
                  let assump_58 := assump_56 assump_109
                  apply False.elim assump_58
          case inr assump_17 =>
            cases assump_17
            case inl assump_62 =>
              cases assump_15
              case intro assump_66 assump_67 =>
                cases assump_67
                case intro assump_70 assump_71 =>
                  apply Or.inl
                  intro assump_76
                  have assump_110 : (p6 → True) := by
                    intro assump_80
                    apply True.intro
                  let assump_79 := assump_76 assump_110
                  have assump_111 : True := by
                    apply True.intro
                  let assump_81 := assump_79 assump_111
                  apply False.elim assump_81
            case inr assump_63 =>
              cases assump_15
              case intro assump_87 assump_88 =>
                cases assump_88
                case intro assump_91 assump_92 =>
                  apply Or.inl
                  intro assump_97
                  have assump_112 : (p6 → True) := by
                    intro assump_101
                    apply True.intro
                  let assump_100 := assump_97 assump_112
                  have assump_113 : True := by
                    apply True.intro
                  let assump_102 := assump_100 assump_113
                  apply False.elim assump_102


variable (p1 p4 p7 p2 p0 : Prop)
theorem file66_84871 : ((((((p1 ∧ p1) ∨ (p2 → True)) → False) → (((p7 → False) ∧ (p0 → p4)) → False)) → False) → False) := by
  intro assump_15
  have assump_37 : ((((p1 ∧ p1) ∨ (p2 → True)) → False) → (((p7 → False) ∧ (p0 → p4)) → False)) := by
    intro assump_19
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      have assump_38 : ((p1 ∧ p1) ∨ (p2 → True)) := by
        apply Or.inr
        intro assump_30
        apply True.intro
      let assump_29 := assump_19 assump_38
      apply False.elim assump_29
  let assump_18 := assump_15 assump_37
  apply False.elim assump_18


variable (p0 p7 p3 p6 p4 p1 p5 : Prop)
theorem file66_85524 : ((((((p6 ∧ p3) ∧ (p1 ∧ p4)) ∨ ((p5 → p4) → False)) → (((p7 ∨ p6) ∧ (p3 ∧ p5)) ∨ ((p0 ∨ p0) ∨ (True → True)))) → ((((True → False) ∧ (p3 → False)) ∨ ((p7 → True) → False)) ∧ (((p1 ∧ p7) ∨ (p7 → p3)) → False))) → False) := by
  intro assump_1
  have assump_48 : ((((p6 ∧ p3) ∧ (p1 ∧ p4)) ∨ ((p5 → p4) → False)) → (((p7 ∨ p6) ∧ (p3 ∧ p5)) ∨ ((p0 ∨ p0) ∨ (True → True)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply Or.inr
            apply Or.inr
            intro assump_22
            apply True.intro
    case inr assump_7 =>
      apply Or.inr
      apply Or.inr
      intro assump_25
      apply True.intro
  let assump_4 := assump_1 assump_48
  let assump_26 := And.left assump_4
  cases assump_26
  case inl assump_28 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      have assump_49 : True := by
        apply True.intro
      let assump_37 := assump_30 assump_49
      apply False.elim assump_37
  case inr assump_29 =>
    have assump_50 : (p7 → True) := by
      intro assump_44
      apply True.intro
    let assump_43 := assump_29 assump_50
    apply False.elim assump_43


variable (p6 p3 p4 p7 p1 p2 p0 : Prop)
theorem file66_86921 : (((((p7 ∨ p0) → (p0 → False)) → False) → (((p7 ∨ p4) ∧ (True → False)) ∨ ((p7 → False) ∨ (p7 ∧ p4)))) → ((((p4 → False) → False) ∨ ((p1 → p4) → (p4 → p7))) → (((False ∧ p2) → (p7 → False)) ∨ ((p6 ∨ p4) ∧ (p3 ∧ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  case inr assump_4 =>
    apply Or.inl
    intro assump_21
    intro assump_22
    cases assump_21
    case intro assump_25 assump_26 =>
      apply False.elim assump_25


variable (p3 p1 p5 p4 p6 p2 p0 p7 : Prop)
theorem file66_87602 : (((((False ∧ p4) ∧ (False ∧ p6)) ∧ ((p6 ∨ p6) → (p6 → p6))) ∧ (((p2 ∨ p2) → False) → ((p0 ∧ p5) → False))) → ((((p1 → False) ∨ (True ∧ p2)) ∧ ((p0 ∨ p5) → (p0 ∨ p2))) ∧ (((p0 ∨ p3) ∧ (p7 → False)) ∨ ((True ∨ p2) ∧ (p7 → False))))) := by
  intro assump_10
  apply And.intro
  apply And.intro
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
  intro assump_21
  cases assump_21
  case inl assump_22 =>
    cases assump_10
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            apply False.elim assump_32
  case inr assump_23 =>
    cases assump_10
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            apply False.elim assump_44
  cases assump_10
  case intro assump_48 assump_49 =>
    cases assump_48
    case intro assump_50 assump_51 =>
      cases assump_50
      case intro assump_52 assump_53 =>
        cases assump_52
        case intro assump_54 assump_55 =>
          apply False.elim assump_54


variable (p4 p0 p5 p3 p2 p7 p1 : Prop)
theorem file66_89184 : (((((p5 → False) → False) ∨ ((p1 ∧ p1) → (p1 → p7))) ∧ (((p3 ∨ p3) ∧ (False → p7)) ∧ ((p7 → p3) → False))) → ((((True ∧ p3) ∨ (p4 → False)) ∧ ((p7 → True) ∨ (p1 ∧ False))) ∧ (((p2 ∨ p3) → (p3 → False)) ∧ ((True ∨ p5) → (p4 → p0))))) := by
  intro assump_35
  apply And.intro
  apply And.intro
  cases assump_35
  case intro assump_36 assump_37 =>
    cases assump_36
    case inl assump_38 =>
      cases assump_37
      case intro assump_42 assump_43 =>
        cases assump_42
        case intro assump_44 assump_45 =>
          cases assump_44
          case inl assump_46 =>
            apply Or.inl
            apply And.intro
            apply True.intro
            exact assump_46
          case inr assump_47 =>
            apply Or.inl
            apply And.intro
            apply True.intro
            exact assump_47
    case inr assump_39 =>
      cases assump_37
      case intro assump_62 assump_63 =>
        cases assump_62
        case intro assump_64 assump_65 =>
          cases assump_64
          case inl assump_66 =>
            apply Or.inl
            apply And.intro
            apply True.intro
            exact assump_66
          case inr assump_67 =>
            apply Or.inl
            apply And.intro
            apply True.intro
            exact assump_67
  cases assump_35
  case intro assump_80 assump_81 =>
    cases assump_80
    case inl assump_82 =>
      cases assump_81
      case intro assump_86 assump_87 =>
        cases assump_86
        case intro assump_88 assump_89 =>
          cases assump_88
          case inl assump_90 =>
            apply Or.inl
            intro assump_98
            apply True.intro
          case inr assump_91 =>
            apply Or.inl
            intro assump_105
            apply True.intro
    case inr assump_83 =>
      cases assump_81
      case intro assump_108 assump_109 =>
        cases assump_108
        case intro assump_110 assump_111 =>
          cases assump_110
          case inl assump_112 =>
            apply Or.inl
            intro assump_120
            apply True.intro
          case inr assump_113 =>
            apply Or.inl
            intro assump_127
            apply True.intro
  apply And.intro
  intro assump_128
  intro assump_129
  cases assump_128
  case inl assump_132 =>
    cases assump_35
    case intro assump_136 assump_137 =>
      cases assump_136
      case inl assump_138 =>
        cases assump_137
        case intro assump_142 assump_143 =>
          cases assump_142
          case intro assump_144 assump_145 =>
            cases assump_144
            case inl assump_146 =>
              have assump_436 : (p7 → p3) := by
                intro assump_155
                exact assump_146
              let assump_154 := assump_143 assump_436
              apply False.elim assump_154
            case inr assump_147 =>
              have assump_437 : (p7 → p3) := by
                intro assump_168
                exact assump_147
              let assump_167 := assump_143 assump_437
              apply False.elim assump_167
      case inr assump_139 =>
        cases assump_137
        case intro assump_176 assump_177 =>
          cases assump_176
          case intro assump_178 assump_179 =>
            cases assump_178
            case inl assump_180 =>
              have assump_438 : (p7 → p3) := by
                intro assump_189
                exact assump_180
              let assump_188 := assump_177 assump_438
              apply False.elim assump_188
            case inr assump_181 =>
              have assump_439 : (p7 → p3) := by
                intro assump_202
                exact assump_181
              let assump_201 := assump_177 assump_439
              apply False.elim assump_201
  case inr assump_133 =>
    cases assump_35
    case intro assump_210 assump_211 =>
      cases assump_210
      case inl assump_212 =>
        cases assump_211
        case intro assump_216 assump_217 =>
          cases assump_216
          case intro assump_218 assump_219 =>
            cases assump_218
            case inl assump_220 =>
              have assump_440 : (p7 → p3) := by
                intro assump_229
                exact assump_220
              let assump_228 := assump_217 assump_440
              apply False.elim assump_228
            case inr assump_221 =>
              have assump_441 : (p7 → p3) := by
                intro assump_242
                exact assump_221
              let assump_241 := assump_217 assump_441
              apply False.elim assump_241
      case inr assump_213 =>
        cases assump_211
        case intro assump_250 assump_251 =>
          cases assump_250
          case intro assump_252 assump_253 =>
            cases assump_252
            case inl assump_254 =>
              have assump_442 : (p7 → p3) := by
                intro assump_263
                exact assump_254
              let assump_262 := assump_251 assump_442
              apply False.elim assump_262
            case inr assump_255 =>
              have assump_443 : (p7 → p3) := by
                intro assump_276
                exact assump_255
              let assump_275 := assump_251 assump_443
              apply False.elim assump_275
  intro assump_282
  intro assump_283
  cases assump_282
  case inl assump_286 =>
    cases assump_35
    case intro assump_290 assump_291 =>
      cases assump_290
      case inl assump_292 =>
        cases assump_291
        case intro assump_296 assump_297 =>
          cases assump_296
          case intro assump_298 assump_299 =>
            cases assump_298
            case inl assump_300 =>
              have assump_444 : (p7 → p3) := by
                intro assump_309
                exact assump_300
              let assump_308 := assump_297 assump_444
              apply False.elim assump_308
            case inr assump_301 =>
              have assump_445 : (p7 → p3) := by
                intro assump_322
                exact assump_301
              let assump_321 := assump_297 assump_445
              apply False.elim assump_321
      case inr assump_293 =>
        cases assump_291
        case intro assump_330 assump_331 =>
          cases assump_330
          case intro assump_332 assump_333 =>
            cases assump_332
            case inl assump_334 =>
              have assump_446 : (p7 → p3) := by
                intro assump_343
                exact assump_334
              let assump_342 := assump_331 assump_446
              apply False.elim assump_342
            case inr assump_335 =>
              have assump_447 : (p7 → p3) := by
                intro assump_356
                exact assump_335
              let assump_355 := assump_331 assump_447
              apply False.elim assump_355
  case inr assump_287 =>
    cases assump_35
    case intro assump_364 assump_365 =>
      cases assump_364
      case inl assump_366 =>
        cases assump_365
        case intro assump_370 assump_371 =>
          cases assump_370
          case intro assump_372 assump_373 =>
            cases assump_372
            case inl assump_374 =>
              have assump_448 : (p7 → p3) := by
                intro assump_383
                exact assump_374
              let assump_382 := assump_371 assump_448
              apply False.elim assump_382
            case inr assump_375 =>
              have assump_449 : (p7 → p3) := by
                intro assump_396
                exact assump_375
              let assump_395 := assump_371 assump_449
              apply False.elim assump_395
      case inr assump_367 =>
        cases assump_365
        case intro assump_404 assump_405 =>
          cases assump_404
          case intro assump_406 assump_407 =>
            cases assump_406
            case inl assump_408 =>
              have assump_450 : (p7 → p3) := by
                intro assump_417
                exact assump_408
              let assump_416 := assump_405 assump_450
              apply False.elim assump_416
            case inr assump_409 =>
              have assump_451 : (p7 → p3) := by
                intro assump_430
                exact assump_409
              let assump_429 := assump_405 assump_451
              apply False.elim assump_429


variable (p4 p0 p6 p5 p3 p1 p7 : Prop)
theorem file66_97527 : ((((((p7 ∨ p6) → (p0 ∧ True)) ∧ ((p4 ∧ p6) ∧ (p5 ∧ p3))) → (((p5 ∨ p1) → (p3 → p0)) ∧ ((p3 → True) ∨ (p4 → p4)))) → False) → False) := by
  intro assump_1
  have assump_88 : ((((p7 ∨ p6) → (p0 ∧ True)) ∧ ((p4 ∧ p6) ∧ (p5 ∧ p3))) → (((p5 ∨ p1) → (p3 → p0)) ∧ ((p3 → True) ∨ (p4 → p4)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_19
            case intro assump_26 assump_27 =>
              have assump_89 : (p7 ∨ p6) := by
                apply Or.inr
                exact assump_21
              let assump_36 := assump_14 assump_89
              let assump_37 := And.left assump_36
              exact assump_37
    case inr assump_11 =>
      cases assump_5
      case intro assump_41 assump_42 =>
        cases assump_42
        case intro assump_45 assump_46 =>
          cases assump_45
          case intro assump_47 assump_48 =>
            cases assump_46
            case intro assump_53 assump_54 =>
              have assump_90 : (p7 ∨ p6) := by
                apply Or.inr
                exact assump_48
              let assump_63 := assump_41 assump_90
              let assump_64 := And.left assump_63
              exact assump_64
    cases assump_5
    case intro assump_66 assump_67 =>
      cases assump_67
      case intro assump_70 assump_71 =>
        cases assump_70
        case intro assump_72 assump_73 =>
          cases assump_71
          case intro assump_78 assump_79 =>
            apply Or.inl
            intro assump_84
            apply True.intro
  let assump_4 := assump_1 assump_88
  apply False.elim assump_4


variable (p6 p0 p1 p3 p7 p2 p4 : Prop)
theorem file66_99452 : ((((((True ∧ p4) ∧ (p0 ∧ p3)) → ((True ∧ p1) → False)) ∨ (((p4 ∧ p4) → (False → p4)) → ((p6 ∨ p6) ∧ (p4 → p1)))) ∧ ((((p2 ∨ p2) → False) ∧ ((False ∧ p7) → False)) ∧ (((p6 ∧ False) ∨ (False → p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_44 : ((p6 ∧ False) ∨ (False → p6)) := by
            apply Or.inr
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_9 assump_44
          apply False.elim assump_18
    case inr assump_5 =>
      cases assump_3
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          have assump_45 : ((p6 ∧ False) ∨ (False → p6)) := by
            apply Or.inr
            intro assump_38
            apply False.elim assump_38
          let assump_37 := assump_28 assump_45
          apply False.elim assump_37


variable (p6 p4 p2 p0 p3 p7 : Prop)
theorem file66_100599 : ((((((p2 ∨ p3) ∧ (p3 ∨ p2)) → ((p4 ∧ p2) → (True → False))) → (((p2 ∨ p6) ∨ (p7 ∧ p6)) → ((p3 ∧ p0) → (p2 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p2 ∨ p3) ∧ (p3 ∨ p2)) → ((p4 ∧ p2) → (True → False))) → (((p2 ∨ p6) ∨ (p7 ∧ p6)) → ((p3 ∧ p0) → (p2 ∨ p6)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case inl assump_14 =>
        cases assump_14
        case inl assump_16 =>
          apply Or.inl
          exact assump_16
        case inr assump_17 =>
          apply Or.inr
          exact assump_17
      case inr assump_15 =>
        cases assump_15
        case intro assump_26 assump_27 =>
          apply Or.inr
          exact assump_27
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p7 p6 p5 p1 p2 : Prop)
theorem file66_101501 : (((((False ∧ True) ∧ (p2 → p7)) → ((p6 → False) ∧ (p5 → p1))) → False) → False) := by
  intro assump_1
  have assump_27 : (((False ∧ True) ∧ (p2 → p7)) → ((p6 → False) ∧ (p5 → p1))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
    intro assump_15
    cases assump_5
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_20
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p5 p3 p0 p6 p7 : Prop)
theorem file66_102195 : ((((((True ∨ p0) → (p0 ∧ p7)) → ((True ∧ p6) → False)) → (((p0 → False) ∧ (False ∨ p0)) → False)) ∧ ((((p7 → p7) → False) → ((True ∨ p3) ∨ (p5 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p7 → p7) → False) → ((True ∨ p3) ∨ (p5 → False))) := by
      intro assump_9
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p7 p2 p6 p5 p1 : Prop)
theorem file66_102733 : (((((p5 → False) ∧ (p7 ∧ p1)) ∧ ((False → p3) ∨ (p2 ∧ p5))) → (((p2 ∨ True) ∧ (False ∧ False)) → ((p6 → True) ∨ (p7 → p6)))) ∨ ((((p5 → p1) → (True ∧ p6)) ∧ ((p1 ∧ p7) ∨ (p1 ∨ False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    case inr assump_6 =>
      cases assump_4
      case intro assump_15 assump_16 =>
        apply False.elim assump_15


variable (p4 p6 p3 p5 p7 p0 p2 : Prop)
theorem file66_103356 : ((((((False → False) → False) → ((True ∨ p4) ∨ (p7 ∧ False))) ∨ (((p7 ∨ p6) ∧ (p2 → False)) ∨ ((p6 ∨ p5) ∨ (p3 → p0)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) → False) → ((True ∨ p4) ∨ (p7 ∧ False))) ∨ (((p7 ∨ p6) ∧ (p2 → False)) ∨ ((p6 ∨ p5) ∨ (p3 → p0)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p0 p6 p7 p1 p5 : Prop)
theorem file66_103876 : ((((((p5 ∨ False) → (True ∨ p5)) ∧ ((p1 ∧ p6) ∧ (p5 → False))) ∨ (((p2 ∧ True) → (p0 ∨ True)) ∨ ((p7 → False) ∨ (True ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p5 ∨ False) → (True ∨ p5)) ∧ ((p1 ∧ p6) ∧ (p5 → False))) ∨ (((p2 ∧ True) → (p0 ∨ True)) ∨ ((p7 → False) ∨ (True ∧ p2)))) := by
    apply Or.inr
    apply Or.inl
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p7 p0 p5 p3 p1 p6 p4 : Prop)
theorem file66_104479 : (((((p1 ∧ False) → (p3 ∧ p2)) → ((p0 → True) ∨ (False → p4))) ∨ (((False ∨ p4) ∨ (p0 → False)) ∧ ((p6 → False) ∨ (p6 → p7)))) ∨ ((((True → False) ∧ (p6 → p7)) ∨ ((p2 ∨ p7) → False)) ∨ (((p2 ∨ p1) → False) → ((p0 → p5) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p2 p3 p0 p6 : Prop)
theorem file66_104867 : (((((p2 ∧ p6) ∨ (True ∧ p0)) → ((True ∨ p6) ∨ (p3 ∧ False))) → False) → False) := by
  intro assump_1
  have assump_23 : (((p2 ∧ p6) ∨ (True ∧ p0)) → ((True ∨ p6) ∨ (p3 ∧ False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p4 p0 p1 p5 p6 p3 p7 : Prop)
theorem file66_105523 : ((((((p6 → p6) ∨ (p0 → False)) ∨ ((p4 → False) → (p3 ∨ p4))) → False) ∨ ((((p5 → False) → (p1 → False)) ∨ ((p3 → False) → False)) ∧ (((p7 ∧ p6) ∨ (p1 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_33 : (((p6 → p6) ∨ (p0 → False)) ∨ ((p4 → False) → (p3 ∨ p4))) := by
      apply Or.inl
      apply Or.inl
      intro assump_7
      exact assump_7
    let assump_6 := assump_2 assump_33
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        have assump_34 : ((p7 ∧ p6) ∨ (p1 ∨ True)) := by
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_21 := assump_14 assump_34
        apply False.elim assump_21
      case inr assump_16 =>
        have assump_35 : ((p7 ∧ p6) ∨ (p1 ∨ True)) := by
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_29 := assump_14 assump_35
        apply False.elim assump_29


variable (p6 p3 p4 p5 p1 p7 p2 : Prop)
theorem file66_106640 : ((((((p2 ∧ p4) ∧ (p6 → False)) ∧ ((p7 ∧ p3) ∧ (True ∨ p4))) ∧ (((p7 ∨ p5) → False) ∧ ((p6 ∨ p2) → False))) ∧ ((((p4 ∨ True) ∨ (True ∧ False)) → False) ∧ (((p2 ∨ p5) ∧ (p5 ∨ p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_19
                case inl assump_26 =>
                  cases assump_5
                  case intro assump_30 assump_31 =>
                    cases assump_3
                    case intro assump_36 assump_37 =>
                      have assump_66 : ((p4 ∨ True) ∨ (True ∧ False)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_11
                      let assump_43 := assump_36 assump_66
                      apply False.elim assump_43
                case inr assump_27 =>
                  cases assump_5
                  case intro assump_49 assump_50 =>
                    cases assump_3
                    case intro assump_55 assump_56 =>
                      have assump_67 : ((p4 ∨ True) ∨ (True ∧ False)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_27
                      let assump_62 := assump_55 assump_67
                      apply False.elim assump_62


variable (p7 p1 p4 : Prop)
theorem file66_108412 : (((((p7 → p7) ∨ (p1 ∧ p4)) ∨ ((False ∨ p1) → (p4 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p7 → p7) ∨ (p1 ∧ p4)) ∨ ((False ∨ p1) → (p4 ∨ p4))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p6 p7 p5 p2 p0 p3 : Prop)
theorem file66_108790 : ((((((p3 → True) ∨ (p0 ∧ p6)) ∨ ((p2 → False) ∨ (p1 ∧ p3))) ∧ (((p1 → False) → (p7 ∧ p7)) → ((p6 ∧ True) → (p5 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p3 → True) ∨ (p0 ∧ p6)) ∨ ((p2 → False) ∨ (p1 ∧ p3))) ∧ (((p1 → False) → (p7 ∧ p7)) → ((p6 ∧ True) → (p5 → True)))) := by
    apply And.intro
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
    intro assump_6
    intro assump_7
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p7 p0 : Prop)
theorem file66_109386 : (((((p0 ∨ p7) ∧ (p7 → p7)) ∨ ((p7 → False) ∧ (p2 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p0 ∨ p7) ∧ (p7 → p7)) ∨ ((p7 → False) ∧ (p2 ∨ True))) := by
    apply Or.inr
    apply And.intro
    intro assump_5
    have assump_20 : (((p0 ∨ p7) ∧ (p7 → p7)) ∨ ((p7 → False) ∧ (p2 ∨ True))) := by
      apply Or.inl
      apply And.intro
      apply Or.inr
      exact assump_5
      intro assump_10
      exact assump_10
    let assump_9 := assump_1 assump_20
    apply False.elim assump_9
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p1 p3 p4 p7 p0 p5 : Prop)
theorem file66_110068 : (((((p0 ∨ False) ∧ (p4 ∧ p1)) → False) → (((False ∧ p2) ∨ (p7 ∧ p4)) → ((p4 → p4) → (True → p7)))) ∨ ((((p1 ∧ p5) → (True → False)) ∧ ((False ∧ p3) ∨ (p0 → False))) ∧ (((p2 → False) → False) ∧ ((p2 ∧ p7) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      apply False.elim assump_11
  case inr assump_10 =>
    cases assump_10
    case intro assump_15 assump_16 =>
      exact assump_15


variable (p7 p0 p3 p5 p2 p1 : Prop)
theorem file66_110667 : (((((p2 → False) → (p2 → False)) → False) → (((p3 ∧ p2) ∨ (p3 ∧ p7)) ∧ ((p5 ∧ p2) → False))) ∨ ((((p7 ∨ p7) → (False ∨ p0)) ∨ ((True → False) ∨ (True ∧ p3))) ∨ (((p1 → p1) → (p7 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  have assump_41 : ((p2 → False) → (p2 → False)) := by
    intro assump_5
    intro assump_6
    have assump_42 : p2 := by
      exact assump_6
    let assump_11 := assump_5 assump_42
    apply False.elim assump_11
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    have assump_43 : ((p2 → False) → (p2 → False)) := by
      intro assump_28
      intro assump_29
      have assump_44 : p2 := by
        exact assump_29
      let assump_34 := assump_28 assump_44
      apply False.elim assump_34
    let assump_27 := assump_1 assump_43
    apply False.elim assump_27


variable (p1 p5 p6 p0 p7 p3 : Prop)
theorem file66_111638 : ((((((p6 → False) ∨ (p1 → False)) → ((True → False) → False)) ∨ (((p0 ∧ p7) ∧ (p7 → False)) ∨ ((True → p1) → (p1 ∨ True)))) ∧ ((((p0 ∧ p5) ∨ (p5 → p5)) ∨ ((p0 → False) ∨ (p6 ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_49 : (((p0 ∧ p5) ∨ (p5 → p5)) ∨ ((p0 → False) ∨ (p6 ∨ p3))) := by
        apply Or.inl
        apply Or.inr
        intro assump_11
        exact assump_11
      let assump_10 := assump_3 assump_49
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_17 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            have assump_50 : (((p0 ∧ p5) ∨ (p5 → p5)) ∨ ((p0 → False) ∨ (p6 ∨ p3))) := by
              apply Or.inl
              apply Or.inr
              intro assump_32
              exact assump_32
            let assump_31 := assump_3 assump_50
            apply False.elim assump_31
      case inr assump_18 =>
        have assump_51 : (((p0 ∧ p5) ∨ (p5 → p5)) ∨ ((p0 → False) ∨ (p6 ∨ p3))) := by
          apply Or.inl
          apply Or.inr
          intro assump_43
          exact assump_43
        let assump_42 := assump_3 assump_51
        apply False.elim assump_42


variable (p3 p4 p7 p5 p1 p6 : Prop)
theorem file66_113058 : (((((p1 ∨ p1) ∧ (p4 → False)) ∧ ((p3 ∧ p5) → (p6 → p6))) → False) → ((((p7 → p6) → (True → p5)) ∧ ((p4 ∨ True) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_16 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_12 := assump_4 assump_16
    apply False.elim assump_12


variable (p3 p1 p4 p7 p2 : Prop)
theorem file66_113489 : (((((True ∨ p2) → False) ∧ ((p4 ∨ p3) → False)) ∧ (((p2 ∨ p4) → False) ∧ ((p1 ∧ p7) → False))) → ((((False → False) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case intro assump_13 assump_14 =>
        have assump_26 : (True ∨ p2) := by
          apply Or.inl
          apply True.intro
        let assump_22 := assump_7 assump_26
        apply False.elim assump_22


variable (p6 p7 p5 p1 p4 : Prop)
theorem file66_114069 : ((((((p7 → p5) → False) ∧ ((True ∨ p4) → False)) ∧ (((p6 ∨ p7) ∨ (p7 → False)) ∧ ((p1 ∨ p7) ∧ (p7 → p4)))) ∧ ((((False → False) → False) → ((p5 → p1) → False)) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                cases assump_24
                case inl assump_26 =>
                  have assump_178 : (((False → False) → False) → ((p5 → p1) → False)) := by
                    intro assump_35
                    intro assump_36
                    have assump_179 : (False → False) := by
                      intro assump_42
                      apply False.elim assump_42
                    let assump_41 := assump_35 assump_179
                    apply False.elim assump_41
                  let assump_34 := assump_7 assump_178
                  apply False.elim assump_34
                case inr assump_27 =>
                  have assump_180 : (((False → False) → False) → ((p5 → p1) → False)) := by
                    intro assump_58
                    intro assump_59
                    have assump_181 : (False → False) := by
                      intro assump_65
                      apply False.elim assump_65
                    let assump_64 := assump_58 assump_181
                    apply False.elim assump_64
                  let assump_57 := assump_7 assump_180
                  apply False.elim assump_57
            case inr assump_21 =>
              cases assump_17
              case intro assump_76 assump_77 =>
                cases assump_76
                case inl assump_78 =>
                  have assump_182 : (((False → False) → False) → ((p5 → p1) → False)) := by
                    intro assump_87
                    intro assump_88
                    have assump_183 : (False → False) := by
                      intro assump_94
                      apply False.elim assump_94
                    let assump_93 := assump_87 assump_183
                    apply False.elim assump_93
                  let assump_86 := assump_7 assump_182
                  apply False.elim assump_86
                case inr assump_79 =>
                  have assump_184 : (((False → False) → False) → ((p5 → p1) → False)) := by
                    intro assump_110
                    intro assump_111
                    have assump_185 : (False → False) := by
                      intro assump_117
                      apply False.elim assump_117
                    let assump_116 := assump_110 assump_185
                    apply False.elim assump_116
                  let assump_109 := assump_7 assump_184
                  apply False.elim assump_109
          case inr assump_19 =>
            cases assump_17
            case intro assump_128 assump_129 =>
              cases assump_128
              case inl assump_130 =>
                have assump_186 : (((False → False) → False) → ((p5 → p1) → False)) := by
                  intro assump_139
                  intro assump_140
                  have assump_187 : (False → False) := by
                    intro assump_146
                    apply False.elim assump_146
                  let assump_145 := assump_139 assump_187
                  apply False.elim assump_145
                let assump_138 := assump_7 assump_186
                apply False.elim assump_138
              case inr assump_131 =>
                have assump_188 : (((False → False) → False) → ((p5 → p1) → False)) := by
                  intro assump_162
                  intro assump_163
                  have assump_189 : (False → False) := by
                    intro assump_169
                    apply False.elim assump_169
                  let assump_168 := assump_162 assump_189
                  apply False.elim assump_168
                let assump_161 := assump_7 assump_188
                apply False.elim assump_161


variable (p6 p4 p7 p5 p1 p2 : Prop)
theorem file66_118385 : (((((p6 ∧ p1) → (p6 ∨ p6)) ∨ ((p2 → False) → False)) → False) → ((((True ∧ True) → (False ∨ p6)) ∧ ((p7 → False) → (p2 → False))) ∧ (((p5 → False) ∨ (p5 ∨ p6)) ∧ ((False → p4) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_74 : (((p6 ∧ p1) → (p6 ∨ p6)) ∨ ((p2 → False) → False)) := by
      apply Or.inl
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply Or.inl
        exact assump_13
    let assump_11 := assump_1 assump_74
    apply False.elim assump_11
  intro assump_22
  intro assump_23
  have assump_75 : (((p6 ∧ p1) → (p6 ∨ p6)) ∨ ((p2 → False) → False)) := by
    apply Or.inl
    intro assump_31
    cases assump_31
    case intro assump_32 assump_33 =>
      apply Or.inl
      exact assump_32
  let assump_30 := assump_1 assump_75
  apply False.elim assump_30
  apply And.intro
  apply Or.inl
  intro assump_43
  have assump_76 : (((p6 ∧ p1) → (p6 ∨ p6)) ∨ ((p2 → False) → False)) := by
    apply Or.inl
    intro assump_48
    cases assump_48
    case intro assump_49 assump_50 =>
      apply Or.inl
      exact assump_49
  let assump_47 := assump_1 assump_76
  apply False.elim assump_47
  intro assump_58
  have assump_77 : (((p6 ∧ p1) → (p6 ∨ p6)) ∨ ((p2 → False) → False)) := by
    apply Or.inl
    intro assump_64
    cases assump_64
    case intro assump_65 assump_66 =>
      apply Or.inl
      exact assump_65
  let assump_63 := assump_1 assump_77
  apply False.elim assump_63


variable (p6 p1 p2 p0 p7 p3 p5 : Prop)
theorem file66_120002 : (((((p1 ∨ p2) ∨ (p6 → False)) → ((True → False) ∧ (p5 ∧ p3))) ∧ (((p7 ∧ True) ∨ (False → False)) → False)) → ((((True ∧ True) ∧ (p5 ∧ p0)) → ((p3 → False) ∨ (p1 → p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_18 : ((p7 ∧ True) ∨ (False → False)) := by
      apply Or.inr
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_6 assump_18
    apply False.elim assump_11


variable (p0 p3 p4 p5 p1 p2 p6 p7 : Prop)
theorem file66_120542 : (((((p3 ∧ p6) → (p1 → p7)) ∨ ((p4 ∧ p6) ∧ (p3 → False))) → (((False → p1) → False) ∨ ((p1 → p2) ∨ (p3 ∨ p1)))) → ((((p2 → False) → (p0 → p0)) ∧ ((p4 → p4) ∨ (p5 → False))) ∨ (((p7 → False) → (p6 → False)) ∨ ((p4 ∧ p5) → (p6 ∧ p1))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  intro assump_5
  exact assump_5
  apply Or.inl
  intro assump_10
  exact assump_10


variable (p5 p0 p6 : Prop)
theorem file66_120985 : (((((p6 ∨ p0) ∨ (False → False)) ∧ ((p5 ∧ False) → False)) → False) → False) := by
  intro assump_21
  have assump_38 : (((p6 ∨ p0) ∨ (False → False)) ∧ ((p5 ∧ False) → False)) := by
    apply And.intro
    apply Or.inr
    intro assump_25
    apply False.elim assump_25
    intro assump_28
    cases assump_28
    case intro assump_29 assump_30 =>
      apply False.elim assump_30
  let assump_24 := assump_21 assump_38
  apply False.elim assump_24


variable (p7 p6 p4 p5 p0 p3 : Prop)
theorem file66_121495 : (((((p0 → p5) ∨ (p7 → False)) ∧ ((p3 ∨ p3) → (False ∧ True))) → (((False ∨ p3) ∧ (p3 ∧ p6)) → False)) ∨ ((((p4 ∨ p4) → (p3 ∨ p7)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply False.elim assump_5
    case inr assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            have assump_39 : (p3 ∨ p3) := by
              apply Or.inl
              exact assump_11
            let assump_25 := assump_18 assump_39
            let assump_26 := And.left assump_25
            apply False.elim assump_26
          case inr assump_20 =>
            have assump_40 : (p3 ∨ p3) := by
              apply Or.inl
              exact assump_11
            let assump_34 := assump_18 assump_40
            let assump_35 := And.left assump_34
            apply False.elim assump_35


variable (p5 p6 p4 p1 p7 p3 : Prop)
theorem file66_122603 : (((((p6 ∧ False) ∧ (p5 ∨ p4)) → ((p1 → False) → (p7 → True))) → False) → ((((p7 → False) → (p3 → p1)) ∧ ((False ∧ p5) → (p6 ∧ p5))) → False)) := by
  intro assump_7
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    have assump_24 : (((p6 ∧ False) ∧ (p5 ∨ p4)) → ((p1 → False) → (p7 → True))) := by
      intro assump_18
      intro assump_19
      intro assump_20
      apply True.intro
    let assump_17 := assump_7 assump_24
    apply False.elim assump_17


variable (p3 p0 p1 p4 p5 : Prop)
theorem file66_123141 : ((((((True → False) → (p5 → False)) ∨ ((p4 ∨ p3) → False)) → False) ∨ ((((p4 → False) ∧ (p1 → p3)) → ((p5 ∨ p5) ∨ (False ∧ p5))) ∧ (((False → False) ∨ (p3 ∧ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_33 : (((True → False) → (p5 → False)) ∨ ((p4 ∨ p3) → False)) := by
      apply Or.inl
      intro assump_7
      intro assump_8
      have assump_34 : True := by
        apply True.intro
      let assump_13 := assump_7 assump_34
      apply False.elim assump_13
    let assump_6 := assump_2 assump_33
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_20 assump_21 =>
      have assump_35 : ((False → False) ∨ (p3 ∧ p0)) := by
        apply Or.inl
        intro assump_27
        apply False.elim assump_27
      let assump_26 := assump_21 assump_35
      apply False.elim assump_26


variable (p2 p4 : Prop)
theorem file66_124076 : ((((((False → p4) ∨ (p2 → False)) → False) → False) → False) → False) := by
  intro assump_21
  have assump_38 : ((((False → p4) ∨ (p2 → False)) → False) → False) := by
    intro assump_25
    have assump_39 : ((False → p4) ∨ (p2 → False)) := by
      apply Or.inl
      intro assump_29
      apply False.elim assump_29
    let assump_28 := assump_25 assump_39
    apply False.elim assump_28
  let assump_24 := assump_21 assump_38
  apply False.elim assump_24


