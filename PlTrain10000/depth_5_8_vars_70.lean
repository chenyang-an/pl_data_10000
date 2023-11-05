variable (p1 p5 p2 p7 p4 p0 p6 : Prop)
theorem file70_47 : (((((p0 ∧ p2) → (p0 ∨ p4)) ∨ ((p1 ∨ p4) → False)) ∨ (((p0 ∧ p5) → False) ∧ ((p5 ∧ p0) → (False → False)))) ∨ ((((p1 → p2) → (p7 ∨ p6)) → ((p5 ∧ True) → False)) → (((p2 ∨ p1) ∧ (False ∧ p4)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    exact assump_2


variable (p0 p5 p4 p1 p6 p3 p7 : Prop)
theorem file70_466 : (((((p3 ∧ p7) ∨ (p7 ∧ p1)) ∧ ((p4 ∧ False) → (True → False))) → (((p3 → p4) → False) ∧ ((p4 → False) ∨ (p4 → p6)))) → ((((p7 ∨ p0) ∧ (p6 ∨ p4)) ∧ ((False → False) → (False → False))) ∨ (((p5 → False) ∧ (True → False)) → ((p5 → True) ∨ (False ∧ p1))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inl
    intro assump_11
    apply True.intro


variable (p7 p6 p5 p4 p2 : Prop)
theorem file70_939 : ((((((True ∨ False) ∨ (p2 → True)) ∨ ((p6 → False) → (p7 → False))) ∨ (((p4 → False) ∧ (p5 ∧ False)) → ((p2 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ False) ∨ (p2 → True)) ∨ ((p6 → False) → (p7 → False))) ∨ (((p4 → False) ∧ (p5 ∧ False)) → ((p2 → False) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p6 p3 p5 p7 p4 p2 : Prop)
theorem file70_1474 : ((((((p3 → False) → (p4 ∧ False)) ∨ ((True → p2) ∧ (p7 → False))) ∨ (((p2 → p2) ∧ (True → p1)) ∨ ((p4 → False) → (p6 → False)))) ∧ ((((p4 → False) ∨ (p5 ∨ True)) → ((True → True) ∨ (p3 ∨ p6))) → (((False → False) → False) ∧ ((p1 ∧ True) ∧ (p1 → p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_126 : (((p4 → False) ∨ (p5 ∨ True)) → ((True → True) ∨ (p3 ∨ p6))) := by
          intro assump_13
          cases assump_13
          case inl assump_14 =>
            apply Or.inl
            intro assump_18
            apply True.intro
          case inr assump_15 =>
            cases assump_15
            case inl assump_19 =>
              apply Or.inl
              intro assump_23
              apply True.intro
            case inr assump_20 =>
              apply Or.inl
              intro assump_26
              apply True.intro
        let assump_12 := assump_3 assump_126
        let assump_27 := And.left assump_12
        have assump_127 : (False → False) := by
          intro assump_29
          apply False.elim assump_29
        let assump_28 := assump_27 assump_127
        apply False.elim assump_28
      case inr assump_7 =>
        cases assump_7
        case intro assump_35 assump_36 =>
          have assump_128 : (((p4 → False) ∨ (p5 ∨ True)) → ((True → True) ∨ (p3 ∨ p6))) := by
            intro assump_44
            cases assump_44
            case inl assump_45 =>
              apply Or.inl
              intro assump_49
              apply True.intro
            case inr assump_46 =>
              cases assump_46
              case inl assump_50 =>
                apply Or.inl
                intro assump_54
                apply True.intro
              case inr assump_51 =>
                apply Or.inl
                intro assump_57
                apply True.intro
          let assump_43 := assump_3 assump_128
          let assump_58 := And.left assump_43
          have assump_129 : (False → False) := by
            intro assump_60
            apply False.elim assump_60
          let assump_59 := assump_58 assump_129
          apply False.elim assump_59
    case inr assump_5 =>
      cases assump_5
      case inl assump_66 =>
        cases assump_66
        case intro assump_68 assump_69 =>
          have assump_130 : (((p4 → False) ∨ (p5 ∨ True)) → ((True → True) ∨ (p3 ∨ p6))) := by
            intro assump_77
            cases assump_77
            case inl assump_78 =>
              apply Or.inl
              intro assump_82
              apply True.intro
            case inr assump_79 =>
              cases assump_79
              case inl assump_83 =>
                apply Or.inl
                intro assump_87
                apply True.intro
              case inr assump_84 =>
                apply Or.inl
                intro assump_90
                apply True.intro
          let assump_76 := assump_3 assump_130
          let assump_91 := And.left assump_76
          have assump_131 : (False → False) := by
            intro assump_93
            apply False.elim assump_93
          let assump_92 := assump_91 assump_131
          apply False.elim assump_92
      case inr assump_67 =>
        have assump_132 : (((p4 → False) ∨ (p5 ∨ True)) → ((True → True) ∨ (p3 ∨ p6))) := by
          intro assump_104
          cases assump_104
          case inl assump_105 =>
            apply Or.inl
            intro assump_109
            apply True.intro
          case inr assump_106 =>
            cases assump_106
            case inl assump_110 =>
              apply Or.inl
              intro assump_114
              apply True.intro
            case inr assump_111 =>
              apply Or.inl
              intro assump_117
              apply True.intro
        let assump_103 := assump_3 assump_132
        let assump_118 := And.left assump_103
        have assump_133 : (False → False) := by
          intro assump_120
          apply False.elim assump_120
        let assump_119 := assump_118 assump_133
        apply False.elim assump_119


variable (p6 p2 p5 p7 p3 p4 p0 : Prop)
theorem file70_5715 : ((((((False ∧ False) ∧ (p0 ∨ p5)) ∧ ((p3 ∨ True) ∧ (p5 → p2))) ∧ (((p6 → False) → False) → False)) ∧ ((((p4 ∨ False) → (False → False)) ∨ ((p7 ∨ p4) ∧ (p5 ∨ False))) → False)) → False) := by
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
            apply False.elim assump_10


variable (p1 p3 p0 p7 p4 p2 p6 p5 : Prop)
theorem file70_6325 : (((((p1 ∨ p7) ∨ (True ∨ p3)) → False) → (((False → p2) ∧ (p1 ∨ p5)) ∨ ((p6 ∧ p0) ∧ (p5 ∨ p5)))) ∨ ((((p6 → False) → (True ∨ p4)) → ((p4 ∨ True) → (p1 ∧ p5))) ∧ (((p0 → False) ∨ (p3 → True)) ∧ ((p0 → True) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p1 ∨ p7) ∨ (True ∨ p3)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p3 p2 p1 p6 p7 : Prop)
theorem file70_6808 : (((((p3 → False) → False) → False) ∧ (((True → True) → False) ∧ ((p2 → False) ∧ (p7 → False)))) → ((((p3 ∧ False) ∧ (p1 → False)) ∧ ((p1 → True) → (p6 ∨ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8


variable (p0 p4 p5 p3 p7 : Prop)
theorem file70_7276 : (((((p3 ∧ p7) → (False ∨ p3)) → ((True ∨ p5) ∨ (p4 ∨ p0))) → False) → ((((False → False) → False) → ((p5 ∨ p0) → False)) → False)) := by
  intro assump_1
  intro assump_2
  have assump_14 : (((p3 ∧ p7) → (False ∨ p3)) → ((True ∨ p5) ∨ (p4 ∨ p0))) := by
    intro assump_8
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p3 p4 p7 p5 p0 p6 p1 p2 : Prop)
theorem file70_7734 : (((((True ∨ p3) → (p0 → p5)) ∧ ((p2 → p6) ∧ (False ∧ p3))) ∧ (((p1 → False) ∨ (p7 ∧ p2)) ∨ ((p7 → False) ∧ (p4 ∨ False)))) → ((((False → False) → (p5 ∨ p4)) → False) → (((p5 → p4) → (p6 → False)) ∧ ((p5 ∨ p1) ∨ (False → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  cases assump_1
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_14
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          apply False.elim assump_21
  cases assump_1
  case intro assump_27 assump_28 =>
    cases assump_27
    case intro assump_29 assump_30 =>
      cases assump_30
      case intro assump_33 assump_34 =>
        cases assump_34
        case intro assump_37 assump_38 =>
          apply False.elim assump_37


variable (p2 p0 p6 p5 p3 p4 : Prop)
theorem file70_8669 : ((((((p0 ∧ p3) → (True ∨ p5)) ∧ ((p2 ∨ p4) ∧ (p2 → False))) → (((p5 → False) → (p3 ∨ p3)) → ((False ∧ p0) → False))) ∧ ((((p6 → False) ∨ (p3 → False)) → ((False → False) ∨ (False ∧ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p6 → False) ∨ (p3 → False)) → ((False → False) ∨ (False ∧ p5))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
      case inr assump_11 =>
        apply Or.inl
        intro assump_19
        apply False.elim assump_19
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p0 p1 p3 p7 p6 p4 : Prop)
theorem file70_9430 : ((((((p1 ∧ False) ∨ (p6 ∧ p0)) → ((p6 → True) → (p0 → True))) → False) ∧ ((((p7 ∨ p3) ∧ (False ∧ p6)) ∨ ((p0 ∨ p0) → (p7 ∨ p7))) ∧ (((p3 ∧ p0) ∧ (p1 → p4)) → False))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_19
            case intro assump_24 assump_25 =>
              apply False.elim assump_24
          case inr assump_21 =>
            cases assump_19
            case intro assump_30 assump_31 =>
              apply False.elim assump_30
      case inr assump_17 =>
        have assump_47 : (((p1 ∧ False) ∨ (p6 ∧ p0)) → ((p6 → True) → (p0 → True))) := by
          intro assump_41
          intro assump_42
          intro assump_43
          apply True.intro
        let assump_40 := assump_10 assump_47
        apply False.elim assump_40


variable (p0 p2 p1 p4 : Prop)
theorem file70_10533 : ((((((p2 ∨ p0) → False) → False) → (((p4 → True) ∨ (p0 → False)) ∨ ((p4 → False) → (p1 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p2 ∨ p0) → False) → False) → (((p4 → True) ∨ (p0 → False)) ∨ ((p4 → False) → (p1 ∨ p0)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p3 p2 p5 p7 p4 : Prop)
theorem file70_11007 : ((((((p7 ∧ False) → False) ∨ ((p4 → False) → (p5 → p4))) ∨ (((p7 → False) ∨ (p3 ∧ p5)) ∨ ((p5 ∨ p2) ∧ (p5 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p7 ∧ False) → False) ∨ ((p4 → False) → (p5 → p4))) ∨ (((p7 → False) ∨ (p3 ∧ p5)) ∨ ((p5 ∨ p2) ∧ (p5 ∨ p0)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p1 p6 : Prop)
theorem file70_11557 : ((((((True ∨ p1) ∨ (p1 ∧ p7)) → False) → False) ∧ ((((False → False) ∨ (p7 → False)) ∨ ((p6 → p6) ∧ (p7 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((False → False) ∨ (p7 → False)) ∨ ((p6 → p6) ∧ (p7 → True))) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p7 p5 p4 p0 p3 p1 p2 : Prop)
theorem file70_12077 : ((((((p2 → p1) → (p0 ∨ False)) ∧ ((p4 → p0) → (p1 → p5))) → (((True ∨ False) → False) → ((True ∧ p1) → (True ∨ p1)))) → ((((True ∨ p0) → False) ∧ ((p3 ∧ True) ∨ (p1 → False))) ∧ (((p2 → p7) → False) ∧ ((p7 ∨ p7) ∧ (p5 ∨ p7))))) → False) := by
  intro assump_10
  have assump_37 : ((((p2 → p1) → (p0 ∨ False)) ∧ ((p4 → p0) → (p1 → p5))) → (((True ∨ False) → False) → ((True ∧ p1) → (True ∨ p1)))) := by
    intro assump_14
    intro assump_15
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      cases assump_14
      case intro assump_25 assump_26 =>
        apply Or.inl
        apply True.intro
  let assump_13 := assump_10 assump_37
  let assump_31 := And.left assump_13
  let assump_32 := And.left assump_31
  have assump_38 : (True ∨ p0) := by
    apply Or.inl
    apply True.intro
  let assump_33 := assump_32 assump_38
  apply False.elim assump_33


variable (p5 p4 p1 p7 p6 p2 : Prop)
theorem file70_13023 : (((((p1 → p7) ∨ (p6 → False)) → ((p2 → p2) ∨ (p6 ∨ p1))) ∨ (((True → False) ∨ (False → False)) ∨ ((p5 ∧ p5) ∧ (p5 → False)))) ∨ ((((False ∨ False) ∨ (p5 ∧ p4)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    exact assump_6
  case inr assump_3 =>
    apply Or.inl
    intro assump_11
    exact assump_11


variable (p0 p5 p4 p6 p3 : Prop)
theorem file70_13487 : ((((((False → False) ∧ (p6 → True)) → ((False → False) ∨ (False → False))) → (((p4 ∨ True) ∨ (p6 ∨ p0)) → ((p3 → False) ∧ (p5 → False)))) ∧ ((((p5 ∧ p5) ∨ (p5 → p6)) → False) ∨ (((p0 ∧ p4) ∧ (True ∧ False)) ∧ ((p4 → p0) ∧ (p4 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_38 : ((p5 ∧ p5) ∨ (p5 → p6)) := by
        apply Or.inr
        intro assump_11
        have assump_39 : ((p5 ∧ p5) ∨ (p5 → p6)) := by
          apply Or.inl
          apply And.intro
          exact assump_11
          exact assump_11
        let assump_15 := assump_6 assump_39
        apply False.elim assump_15
      let assump_10 := assump_6 assump_38
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            cases assump_25
            case intro assump_32 assump_33 =>
              apply False.elim assump_33


variable (p6 p2 p5 p7 p3 p0 : Prop)
theorem file70_14658 : ((((((p3 → False) → (p3 → True)) ∨ ((p2 ∧ p5) → False)) ∧ (((p7 ∧ True) ∧ (True ∧ False)) → ((p0 ∨ p6) ∨ (p2 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p3 → False) → (p3 → True)) ∨ ((p2 ∧ p5) → False)) ∧ (((p7 ∧ True) ∧ (True ∧ False)) → ((p0 ∨ p6) ∨ (p2 ∧ p7)))) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          apply False.elim assump_17
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p2 p5 p0 : Prop)
theorem file70_15410 : ((((((p5 → False) ∧ (p1 ∨ p2)) ∨ ((True ∧ p1) → (False → p0))) → False) ∧ ((((p5 ∨ p2) → False) → ((p0 ∧ p2) ∨ (p2 → p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p5 ∨ p2) → False) → ((p0 ∧ p2) ∨ (p2 → p1))) := by
      intro assump_9
      apply Or.inr
      intro assump_12
      have assump_24 : (p5 ∨ p2) := by
        apply Or.inr
        exact assump_12
      let assump_16 := assump_9 assump_24
      apply False.elim assump_16
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p2 p0 p6 p5 p3 p1 p7 : Prop)
theorem file70_16054 : (((((p3 ∧ p6) ∨ (p5 ∨ True)) → False) ∨ (((p2 ∧ p1) ∧ (p1 ∧ p0)) ∨ ((p5 ∨ False) → (p0 ∧ p1)))) → ((((p7 → p7) ∨ (p5 → False)) ∧ ((False ∧ p6) ∨ (False → p0))) ∨ (((p6 ∧ p2) → (p2 ∧ False)) ∨ ((p7 ∨ p1) ∧ (p5 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply And.intro
    apply Or.inl
    intro assump_6
    exact assump_6
    apply Or.inr
    intro assump_9
    apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_15
          case intro assump_22 assump_23 =>
            apply Or.inl
            apply And.intro
            apply Or.inl
            intro assump_28
            exact assump_28
            apply Or.inr
            intro assump_31
            apply False.elim assump_31
    case inr assump_13 =>
      apply Or.inl
      apply And.intro
      apply Or.inl
      intro assump_36
      exact assump_36
      apply Or.inr
      intro assump_39
      apply False.elim assump_39


variable (p6 p2 : Prop)
theorem file70_17241 : ((((((p2 ∨ p6) → (p6 ∨ p2)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p2 ∨ p6) → (p6 ∨ p2)) → False) → False) := by
    intro assump_5
    have assump_23 : ((p2 ∨ p6) → (p6 ∨ p2)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inr
        exact assump_10
      case inr assump_11 =>
        apply Or.inl
        exact assump_11
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p0 p3 p5 p4 p7 p2 : Prop)
theorem file70_17852 : ((((((p5 → False) → False) ∧ ((p5 ∧ True) → False)) ∧ (((p2 → False) ∧ (p5 ∧ p7)) ∧ ((True → p4) ∧ (p6 ∧ True)))) ∧ ((((p4 → p5) ∨ (True ∧ p0)) ∧ ((p4 → True) → False)) ∨ (((p3 ∨ True) → False) ∨ ((True ∧ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_13
              case intro assump_24 assump_25 =>
                cases assump_25
                case intro assump_28 assump_29 =>
                  cases assump_3
                  case inl assump_34 =>
                    cases assump_34
                    case intro assump_36 assump_37 =>
                      cases assump_36
                      case inl assump_38 =>
                        have assump_76 : (p4 → True) := by
                          intro assump_45
                          apply True.intro
                        let assump_44 := assump_37 assump_76
                        apply False.elim assump_44
                      case inr assump_39 =>
                        cases assump_39
                        case intro assump_49 assump_50 =>
                          have assump_77 : (p4 → True) := by
                            intro assump_58
                            apply True.intro
                          let assump_57 := assump_37 assump_77
                          apply False.elim assump_57
                  case inr assump_35 =>
                    cases assump_35
                    case inl assump_62 =>
                      have assump_78 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_66 := assump_62 assump_78
                      apply False.elim assump_66
                    case inr assump_63 =>
                      have assump_79 : (True ∧ p6) := by
                        apply And.intro
                        apply True.intro
                        exact assump_28
                      let assump_72 := assump_63 assump_79
                      apply False.elim assump_72


variable (p0 p6 p7 p3 p4 p5 p2 p1 : Prop)
theorem file70_20303 : (((((p4 → False) → False) ∧ ((p1 ∨ p7) → False)) ∨ (((False → False) → (p6 → False)) → ((False ∧ p6) ∨ (p3 → p5)))) → ((((False → False) ∨ (p5 → p4)) ∨ ((p0 → False) ∧ (p2 ∧ p5))) ∨ (((p4 → False) ∧ (p5 → False)) ∧ ((p3 ∨ p4) ∧ (p3 ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_15
    apply False.elim assump_15


variable (p4 p2 p7 p1 p3 p0 p5 p6 : Prop)
theorem file70_20966 : (((((p6 ∧ p3) ∧ (p7 → True)) → False) ∧ (((p1 → False) ∧ (p3 ∧ p1)) → ((p0 → p0) ∧ (p4 ∧ p5)))) → ((((True → p1) → (True ∨ p5)) ∨ ((p2 ∧ False) ∧ (p0 → False))) ∨ (((p0 → p3) ∧ (p6 → False)) ∨ ((p3 ∧ p5) ∨ (p5 ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply Or.inl
    apply True.intro


variable (p4 p5 p2 p7 p3 p0 p6 : Prop)
theorem file70_21414 : (((((p4 → p0) → (p2 → p5)) ∧ ((False → p6) ∧ (p6 ∧ False))) ∧ (((False → False) ∨ (p0 ∨ p4)) → ((p0 ∧ p0) ∨ (p2 ∨ p5)))) → ((((p2 ∧ p3) → False) ∧ ((p7 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            apply False.elim assump_20


variable (p0 p2 p1 p6 p5 p4 p3 p7 : Prop)
theorem file70_22044 : (((((False → False) → (p0 → False)) → ((p1 ∨ p7) ∨ (p1 ∨ p5))) ∧ (((True → False) ∨ (True → False)) ∨ ((False ∨ p3) ∧ (False ∧ p6)))) → ((((p3 ∨ p5) → False) ∨ ((p4 ∧ p5) → (p5 → False))) ∧ (((p2 → False) ∨ (p7 ∧ p1)) ∨ ((p3 → p2) ∨ (p3 ∨ p1))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        cases assump_12
        case inl assump_13 =>
          have assump_100 : True := by
            apply True.intro
          let assump_18 := assump_8 assump_100
          apply False.elim assump_18
        case inr assump_14 =>
          have assump_101 : True := by
            apply True.intro
          let assump_25 := assump_8 assump_101
          apply False.elim assump_25
      case inr assump_9 =>
        apply Or.inl
        intro assump_31
        cases assump_31
        case inl assump_32 =>
          have assump_102 : True := by
            apply True.intro
          let assump_37 := assump_9 assump_102
          apply False.elim assump_37
        case inr assump_33 =>
          have assump_103 : True := by
            apply True.intro
          let assump_44 := assump_9 assump_103
          apply False.elim assump_44
    case inr assump_7 =>
      cases assump_7
      case intro assump_48 assump_49 =>
        cases assump_48
        case inl assump_50 =>
          apply False.elim assump_50
        case inr assump_51 =>
          cases assump_49
          case intro assump_56 assump_57 =>
            apply False.elim assump_56
  cases assump_1
  case intro assump_60 assump_61 =>
    cases assump_61
    case inl assump_64 =>
      cases assump_64
      case inl assump_66 =>
        apply Or.inl
        apply Or.inl
        intro assump_70
        have assump_104 : True := by
          apply True.intro
        let assump_74 := assump_66 assump_104
        apply False.elim assump_74
      case inr assump_67 =>
        apply Or.inl
        apply Or.inl
        intro assump_80
        have assump_105 : True := by
          apply True.intro
        let assump_84 := assump_67 assump_105
        apply False.elim assump_84
    case inr assump_65 =>
      cases assump_65
      case intro assump_88 assump_89 =>
        cases assump_88
        case inl assump_90 =>
          apply False.elim assump_90
        case inr assump_91 =>
          cases assump_89
          case intro assump_96 assump_97 =>
            apply False.elim assump_96


variable (p5 p4 p2 p1 : Prop)
theorem file70_24655 : (((((p2 ∧ False) ∧ (p1 ∧ p4)) ∨ ((False ∧ True) ∨ (False ∨ False))) → False) → ((((p5 ∨ True) ∧ (p4 → False)) ∧ ((True ∨ p1) → False)) → (((p1 ∧ p2) ∧ (p4 → False)) → False))) := by
  intro assump_22
  intro assump_23
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case intro assump_27 assump_28 =>
      cases assump_23
      case intro assump_35 assump_36 =>
        cases assump_35
        case intro assump_37 assump_38 =>
          cases assump_37
          case inl assump_39 =>
            have assump_67 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_50 := assump_36 assump_67
            apply False.elim assump_50
          case inr assump_40 =>
            have assump_68 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_63 := assump_36 assump_68
            apply False.elim assump_63


variable (p4 p2 p0 p5 : Prop)
theorem file70_25661 : ((((((True ∨ p5) → (p4 → False)) → ((False ∧ p4) → (p2 ∨ True))) ∨ (((p0 → True) → False) ∧ ((p2 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((True ∨ p5) → (p4 → False)) → ((False ∧ p4) → (p2 ∨ True))) ∨ (((p0 → True) → False) ∧ ((p2 → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p5 p1 p3 p6 p4 p0 : Prop)
theorem file70_26229 : (((((p6 ∨ p5) ∧ (p5 ∧ p5)) ∧ ((False ∨ p6) → False)) ∧ (((p1 → p1) → (p5 → True)) → False)) → ((((p6 ∨ p3) → False) ∨ ((False → False) → (p2 ∨ False))) ∧ (((p4 → False) ∧ (p0 ∧ p0)) → False))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case intro assump_12 assump_13 =>
            apply Or.inl
            intro assump_22
            cases assump_22
            case inl assump_23 =>
              have assump_131 : ((p1 → p1) → (p5 → True)) := by
                intro assump_29
                intro assump_30
                apply True.intro
              let assump_28 := assump_3 assump_131
              apply False.elim assump_28
            case inr assump_24 =>
              have assump_132 : ((p1 → p1) → (p5 → True)) := by
                intro assump_38
                intro assump_39
                apply True.intro
              let assump_37 := assump_3 assump_132
              apply False.elim assump_37
        case inr assump_9 =>
          cases assump_7
          case intro assump_45 assump_46 =>
            apply Or.inl
            intro assump_55
            cases assump_55
            case inl assump_56 =>
              have assump_133 : ((p1 → p1) → (p5 → True)) := by
                intro assump_62
                intro assump_63
                apply True.intro
              let assump_61 := assump_3 assump_133
              apply False.elim assump_61
            case inr assump_57 =>
              have assump_134 : ((p1 → p1) → (p5 → True)) := by
                intro assump_71
                intro assump_72
                apply True.intro
              let assump_70 := assump_3 assump_134
              apply False.elim assump_70
  intro assump_76
  cases assump_76
  case intro assump_77 assump_78 =>
    cases assump_78
    case intro assump_81 assump_82 =>
      cases assump_1
      case intro assump_87 assump_88 =>
        cases assump_87
        case intro assump_89 assump_90 =>
          cases assump_89
          case intro assump_91 assump_92 =>
            cases assump_91
            case inl assump_93 =>
              cases assump_92
              case intro assump_97 assump_98 =>
                have assump_135 : ((p1 → p1) → (p5 → True)) := by
                  intro assump_108
                  intro assump_109
                  apply True.intro
                let assump_107 := assump_88 assump_135
                apply False.elim assump_107
            case inr assump_94 =>
              cases assump_92
              case intro assump_115 assump_116 =>
                have assump_136 : ((p1 → p1) → (p5 → True)) := by
                  intro assump_126
                  intro assump_127
                  apply True.intro
                let assump_125 := assump_88 assump_136
                apply False.elim assump_125


variable (p6 p0 p7 p1 p5 p3 p4 : Prop)
theorem file70_29341 : ((((((p0 ∧ p3) ∨ (p6 → p7)) ∨ ((p7 ∨ p7) → (p0 → False))) ∨ (((p7 ∨ p7) ∨ (False → False)) ∨ ((p3 ∧ False) → False))) ∧ ((((p5 → p5) → (True ∨ p4)) ∨ ((p0 → p1) ∧ (p3 → p3))) → False)) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case inl assump_22 =>
      cases assump_22
      case inl assump_24 =>
        cases assump_24
        case inl assump_26 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            have assump_115 : (((p5 → p5) → (True ∨ p4)) ∨ ((p0 → p1) ∧ (p3 → p3))) := by
              apply Or.inl
              intro assump_37
              apply Or.inl
              apply True.intro
            let assump_36 := assump_21 assump_115
            apply False.elim assump_36
        case inr assump_27 =>
          have assump_116 : (((p5 → p5) → (True ∨ p4)) ∨ ((p0 → p1) ∧ (p3 → p3))) := by
            apply Or.inl
            intro assump_48
            apply Or.inl
            apply True.intro
          let assump_47 := assump_21 assump_116
          apply False.elim assump_47
      case inr assump_25 =>
        have assump_117 : (((p5 → p5) → (True ∨ p4)) ∨ ((p0 → p1) ∧ (p3 → p3))) := by
          apply Or.inl
          intro assump_59
          apply Or.inl
          apply True.intro
        let assump_58 := assump_21 assump_117
        apply False.elim assump_58
    case inr assump_23 =>
      cases assump_23
      case inl assump_65 =>
        cases assump_65
        case inl assump_67 =>
          cases assump_67
          case inl assump_69 =>
            have assump_118 : (((p5 → p5) → (True ∨ p4)) ∨ ((p0 → p1) ∧ (p3 → p3))) := by
              apply Or.inl
              intro assump_76
              apply Or.inl
              apply True.intro
            let assump_75 := assump_21 assump_118
            apply False.elim assump_75
          case inr assump_70 =>
            have assump_119 : (((p5 → p5) → (True ∨ p4)) ∨ ((p0 → p1) ∧ (p3 → p3))) := by
              apply Or.inl
              intro assump_87
              apply Or.inl
              apply True.intro
            let assump_86 := assump_21 assump_119
            apply False.elim assump_86
        case inr assump_68 =>
          have assump_120 : (((p5 → p5) → (True ∨ p4)) ∨ ((p0 → p1) ∧ (p3 → p3))) := by
            apply Or.inl
            intro assump_98
            apply Or.inl
            apply True.intro
          let assump_97 := assump_21 assump_120
          apply False.elim assump_97
      case inr assump_66 =>
        have assump_121 : (((p5 → p5) → (True ∨ p4)) ∨ ((p0 → p1) ∧ (p3 → p3))) := by
          apply Or.inl
          intro assump_109
          apply Or.inl
          apply True.intro
        let assump_108 := assump_21 assump_121
        apply False.elim assump_108


variable (p7 p3 p5 p4 p0 p6 : Prop)
theorem file70_32206 : ((((((p3 → p4) ∧ (p6 ∧ False)) ∧ ((False → False) → (p6 → False))) → False) → ((((p5 ∧ p0) ∨ (p4 → p4)) → False) ∧ (((p3 ∧ p4) ∧ (p3 → p7)) → False))) → False) := by
  intro assump_1
  have assump_26 : ((((p3 → p4) ∧ (p6 ∧ False)) ∧ ((False → False) → (p6 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
  let assump_4 := assump_1 assump_26
  let assump_18 := And.left assump_4
  have assump_27 : ((p5 ∧ p0) ∨ (p4 → p4)) := by
    apply Or.inr
    intro assump_20
    exact assump_20
  let assump_19 := assump_18 assump_27
  apply False.elim assump_19


variable (p1 p6 p5 p4 : Prop)
theorem file70_33025 : ((((((p6 → False) → False) → ((True ∨ p6) ∨ (p6 → False))) ∨ (((p4 → False) → False) → ((p1 → p1) ∨ (p1 ∧ p5)))) → ((((p6 ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  have assump_19 : ((((p6 → False) → False) → ((True ∨ p6) ∨ (p6 → False))) ∨ (((p4 → False) → False) → ((p1 → p1) ∨ (p1 ∧ p5)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_19
  have assump_20 : (((p6 ∨ True) → False) → False) := by
    intro assump_9
    have assump_21 : (p6 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_12 := assump_9 assump_21
    apply False.elim assump_12
  let assump_8 := assump_4 assump_20
  apply False.elim assump_8


variable (p0 p7 p2 p1 p4 p6 p3 p5 : Prop)
theorem file70_33838 : (((((p0 → False) ∧ (p2 ∧ p5)) → ((p3 → False) → (p1 ∨ True))) ∨ (((p7 → p4) → (False → False)) → ((p6 ∨ p1) → False))) ∨ ((((p0 ∧ p1) ∨ (True → False)) → ((p3 ∨ False) → (False ∨ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_14
  intro assump_15
  cases assump_14
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      apply Or.inr
      apply True.intro


variable (p4 p2 p5 p6 p3 p7 p0 : Prop)
theorem file70_34322 : ((((((True → False) ∧ (p4 → False)) → ((True → False) → False)) → False) ∧ ((((p7 ∧ p2) → (p3 → False)) ∨ ((False → p0) ∨ (p0 ∨ p0))) ∧ (((False → p4) ∨ (p5 ∨ p3)) → ((p6 ∧ p5) ∧ (p2 ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_154 : (((True → False) ∧ (p4 → False)) → ((True → False) → False)) := by
          intro assump_27
          intro assump_28
          cases assump_27
          case intro assump_31 assump_32 =>
            have assump_155 : True := by
              apply True.intro
            let assump_38 := assump_31 assump_155
            apply False.elim assump_38
        let assump_26 := assump_2 assump_154
        apply False.elim assump_26
      case inr assump_9 =>
        cases assump_9
        case inl assump_45 =>
          have assump_156 : (((True → False) ∧ (p4 → False)) → ((True → False) → False)) := by
            intro assump_64
            intro assump_65
            cases assump_64
            case intro assump_68 assump_69 =>
              have assump_157 : True := by
                apply True.intro
              let assump_75 := assump_68 assump_157
              apply False.elim assump_75
          let assump_63 := assump_2 assump_156
          apply False.elim assump_63
        case inr assump_46 =>
          cases assump_46
          case inl assump_82 =>
            have assump_158 : (((True → False) ∧ (p4 → False)) → ((True → False) → False)) := by
              intro assump_101
              intro assump_102
              cases assump_101
              case intro assump_105 assump_106 =>
                have assump_159 : True := by
                  apply True.intro
                let assump_112 := assump_105 assump_159
                apply False.elim assump_112
            let assump_100 := assump_2 assump_158
            apply False.elim assump_100
          case inr assump_83 =>
            have assump_160 : (((True → False) ∧ (p4 → False)) → ((True → False) → False)) := by
              intro assump_136
              intro assump_137
              cases assump_136
              case intro assump_140 assump_141 =>
                have assump_161 : True := by
                  apply True.intro
                let assump_147 := assump_140 assump_161
                apply False.elim assump_147
            let assump_135 := assump_2 assump_160
            apply False.elim assump_135


variable (p7 p5 p4 p3 p1 p6 p2 : Prop)
theorem file70_36918 : ((((((False ∧ p1) ∨ (True → p1)) → ((True → False) ∨ (p1 → p3))) ∧ (((p2 → p4) ∧ (p7 ∧ p1)) ∧ ((p2 → False) ∧ (True → p6)))) ∧ ((((False → p5) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_9
            case intro assump_20 assump_21 =>
              have assump_42 : (((False → p5) → False) → False) := by
                intro assump_29
                have assump_43 : (False → p5) := by
                  intro assump_33
                  apply False.elim assump_33
                let assump_32 := assump_29 assump_43
                apply False.elim assump_32
              let assump_28 := assump_3 assump_42
              apply False.elim assump_28


variable (p0 p3 p4 p1 p7 : Prop)
theorem file70_37971 : (((((p4 ∨ p3) → False) → ((True ∨ p1) ∨ (p7 ∨ p0))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p4 ∨ p3) → False) → ((True ∨ p1) ∨ (p7 ∨ p0))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p5 p6 p7 p1 p2 p0 : Prop)
theorem file70_38341 : (((((p2 → False) ∧ (p5 ∧ p2)) → False) ∨ (((p1 → p3) ∧ (p1 ∧ p6)) → False)) ∨ ((((p5 ∧ p0) → (p3 ∨ False)) ∨ ((p6 → p3) → (p3 → p2))) ∧ (((p1 ∧ p2) → False) ∨ ((p2 ∨ p7) ∧ (False → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      have assump_22 : p2 := by
        exact assump_11
      let assump_18 := assump_6 assump_22
      apply False.elim assump_18


variable (p5 p0 p4 p6 p7 p2 : Prop)
theorem file70_38885 : (((((p5 ∧ p4) ∨ (p0 → p5)) → ((p5 ∨ True) ∨ (p7 → False))) ∧ (((p2 ∧ False) → False) → False)) → ((((p6 ∧ p0) → (p0 → p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_22 : ((p2 ∧ False) → False) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    let assump_11 := assump_6 assump_22
    apply False.elim assump_11


variable (p3 p4 p1 p7 p2 p0 : Prop)
theorem file70_39418 : ((((((p0 → p1) ∧ (p0 ∧ p4)) → ((p7 → p7) ∧ (p7 ∧ p3))) → (((False ∧ False) → (True ∧ True)) ∨ ((p2 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p0 → p1) ∧ (p0 ∧ p4)) → ((p7 → p7) ∧ (p7 ∧ p3))) → (((False ∧ False) → (True ∧ True)) ∨ ((p2 → False) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p7 p0 p3 p2 p5 : Prop)
theorem file70_39962 : ((((((p7 ∨ p2) ∧ (p4 ∧ p5)) ∧ ((p3 ∨ True) ∧ (False → p4))) ∧ (((p5 ∨ True) → False) → ((p0 → False) ∧ (p0 ∧ p0)))) ∧ ((((p5 → False) ∨ (False ∧ p0)) → False) → False)) → False) := by
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
          case inl assump_10 =>
            cases assump_9
            case intro assump_14 assump_15 =>
              cases assump_7
              case intro assump_20 assump_21 =>
                cases assump_20
                case inl assump_22 =>
                  have assump_136 : (((p5 → False) ∨ (False ∧ p0)) → False) := by
                    intro assump_33
                    cases assump_33
                    case inl assump_34 =>
                      have assump_137 : p5 := by
                        exact assump_15
                      let assump_38 := assump_34 assump_137
                      apply False.elim assump_38
                    case inr assump_35 =>
                      cases assump_35
                      case intro assump_42 assump_43 =>
                        apply False.elim assump_42
                  let assump_32 := assump_3 assump_136
                  apply False.elim assump_32
                case inr assump_23 =>
                  have assump_138 : (((p5 → False) ∨ (False ∧ p0)) → False) := by
                    intro assump_58
                    cases assump_58
                    case inl assump_59 =>
                      have assump_139 : p5 := by
                        exact assump_15
                      let assump_63 := assump_59 assump_139
                      apply False.elim assump_63
                    case inr assump_60 =>
                      cases assump_60
                      case intro assump_67 assump_68 =>
                        apply False.elim assump_67
                  let assump_57 := assump_3 assump_138
                  apply False.elim assump_57
          case inr assump_11 =>
            cases assump_9
            case intro assump_76 assump_77 =>
              cases assump_7
              case intro assump_82 assump_83 =>
                cases assump_82
                case inl assump_84 =>
                  have assump_140 : (((p5 → False) ∨ (False ∧ p0)) → False) := by
                    intro assump_95
                    cases assump_95
                    case inl assump_96 =>
                      have assump_141 : p5 := by
                        exact assump_77
                      let assump_100 := assump_96 assump_141
                      apply False.elim assump_100
                    case inr assump_97 =>
                      cases assump_97
                      case intro assump_104 assump_105 =>
                        apply False.elim assump_104
                  let assump_94 := assump_3 assump_140
                  apply False.elim assump_94
                case inr assump_85 =>
                  have assump_142 : (((p5 → False) ∨ (False ∧ p0)) → False) := by
                    intro assump_120
                    cases assump_120
                    case inl assump_121 =>
                      have assump_143 : p5 := by
                        exact assump_77
                      let assump_125 := assump_121 assump_143
                      apply False.elim assump_125
                    case inr assump_122 =>
                      cases assump_122
                      case intro assump_129 assump_130 =>
                        apply False.elim assump_129
                  let assump_119 := assump_3 assump_142
                  apply False.elim assump_119


variable (p6 p2 p7 p0 p1 p5 p4 : Prop)
theorem file70_43801 : (((((p6 → False) ∧ (p1 ∧ p6)) ∧ ((p0 ∧ True) → (p1 → True))) → False) ∨ ((((p2 → False) → (p7 → p6)) ∧ ((p1 ∧ p7) ∧ (p5 ∨ False))) ∧ (((False → False) → (p0 ∧ True)) → ((False ∧ p4) ∧ (False ∧ p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_23 : p6 := by
          exact assump_9
        let assump_19 := assump_4 assump_23
        apply False.elim assump_19


variable (p0 : Prop)
theorem file70_44388 : (((((True ∨ p0) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ p0) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ p0) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p1 p7 p6 p0 p2 p4 : Prop)
theorem file70_44817 : ((((((False ∨ p7) → (p2 ∨ p2)) ∧ ((p2 ∨ True) ∧ (False ∧ p4))) ∧ (((True → False) ∧ (p7 ∧ p3)) → ((p6 ∨ p7) → False))) ∧ ((((p3 ∨ p1) ∨ (True ∧ p0)) ∨ ((p4 → False) ∧ (p2 ∧ p3))) → (((p1 → False) ∨ (p0 ∧ p2)) ∨ ((False ∨ p4) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
          case inr assump_13 =>
            cases assump_11
            case intro assump_22 assump_23 =>
              apply False.elim assump_22


variable (p3 p6 p1 p2 p4 p7 p5 : Prop)
theorem file70_45699 : (((((p6 ∧ False) → (p2 → True)) ∨ ((p4 ∨ False) ∧ (p7 ∧ p4))) → (((False ∧ p3) ∧ (p3 → p1)) → ((True → False) → (True → p4)))) ∧ ((((p6 → False) → (p4 ∨ p3)) → ((False ∧ p3) ∨ (False → p1))) ∧ (((True ∨ p2) ∨ (p5 ∧ True)) ∨ ((p4 ∧ False) ∧ (p4 → False))))) := by
  apply And.intro
  intro assump_5
  intro assump_6
  intro assump_7
  intro assump_8
  cases assump_6
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      apply False.elim assump_15
  apply And.intro
  intro assump_19
  apply Or.inr
  intro assump_22
  apply False.elim assump_22
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p0 p1 p7 p4 p2 p3 p5 : Prop)
theorem file70_46417 : (((((p7 ∨ p1) ∧ (False → p2)) ∧ ((True → False) ∨ (True ∨ p1))) ∧ (((p4 → p0) ∧ (p7 ∨ p5)) ∨ ((p3 ∧ True) ∨ (p2 → p0)))) ∨ ((((p5 ∧ p0) → (p1 ∨ True)) → ((p0 ∧ True) → (p2 → p0))) ∨ (((p4 → False) → (True → p3)) ∧ ((p3 → p0) ∨ (p5 → False))))) := by
  apply Or.inr
  apply Or.inl
  intro assump_9
  intro assump_10
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    exact assump_14


variable (p4 p6 p7 p1 p0 p5 : Prop)
theorem file70_46884 : ((((((p6 → False) → (p5 → False)) → False) ∨ (((p7 → p4) → (p1 → False)) → ((p0 ∨ p5) ∧ (False ∨ False)))) ∧ ((((p4 ∧ True) → (p5 ∨ p1)) → ((p0 ∧ False) → (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_44 : (((p4 ∧ True) → (p5 ∨ p1)) → ((p0 ∧ False) → (p4 → False))) := by
        intro assump_11
        intro assump_12
        intro assump_13
        cases assump_12
        case intro assump_16 assump_17 =>
          apply False.elim assump_17
      let assump_10 := assump_3 assump_44
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_45 : (((p4 ∧ True) → (p5 ∨ p1)) → ((p0 ∧ False) → (p4 → False))) := by
        intro assump_30
        intro assump_31
        intro assump_32
        cases assump_31
        case intro assump_35 assump_36 =>
          apply False.elim assump_36
      let assump_29 := assump_3 assump_45
      apply False.elim assump_29


variable (p7 p3 p0 p4 p1 p2 : Prop)
theorem file70_47954 : (((((p2 → False) ∧ (p1 ∨ p3)) → ((p2 ∨ p2) → (p0 → p2))) ∨ (((p7 → False) → (p2 ∧ p7)) → ((p1 → p4) ∧ (False → False)))) ∨ ((((p7 ∧ p3) ∨ (p7 → False)) ∨ ((p3 → False) → (p1 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        exact assump_6
      case inr assump_15 =>
        exact assump_6
  case inr assump_7 =>
    cases assump_1
    case intro assump_22 assump_23 =>
      cases assump_23
      case inl assump_26 =>
        exact assump_7
      case inr assump_27 =>
        exact assump_7


variable (p1 p4 p7 p3 p5 p2 : Prop)
theorem file70_48721 : ((((((p3 → False) → (p5 → False)) → False) ∨ (((p1 → p5) → False) → ((p1 → p4) → (p3 → False)))) ∧ ((((p3 ∧ False) ∧ (p3 ∧ p7)) → False) → (((p5 ∨ p4) → (p2 → p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_62 : (((p3 ∧ False) ∧ (p3 ∧ p7)) → False) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
      let assump_10 := assump_3 assump_62
      have assump_63 : ((p5 ∨ p4) → (p2 → p2)) := by
        intro assump_21
        intro assump_22
        cases assump_21
        case inl assump_25 =>
          exact assump_22
        case inr assump_26 =>
          exact assump_22
      let assump_20 := assump_10 assump_63
      apply False.elim assump_20
    case inr assump_5 =>
      have assump_64 : (((p3 ∧ False) ∧ (p3 ∧ p7)) → False) := by
        intro assump_39
        cases assump_39
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            apply False.elim assump_43
      let assump_38 := assump_3 assump_64
      have assump_65 : ((p5 ∨ p4) → (p2 → p2)) := by
        intro assump_49
        intro assump_50
        cases assump_49
        case inl assump_53 =>
          exact assump_50
        case inr assump_54 =>
          exact assump_50
      let assump_48 := assump_38 assump_65
      apply False.elim assump_48


variable (p6 : Prop)
theorem file70_50333 : ((((((True → False) → (p6 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → False) → (p6 → False)) → False) → False) := by
    intro assump_5
    have assump_26 : ((True → False) → (p6 → False)) := by
      intro assump_9
      intro assump_10
      have assump_27 : True := by
        apply True.intro
      let assump_15 := assump_9 assump_27
      apply False.elim assump_15
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 : Prop)
theorem file70_50939 : ((((((True ∨ p2) ∨ (p2 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p2) ∨ (p2 → False)) → False) → False) := by
    intro assump_5
    have assump_16 : ((True ∨ p2) ∨ (p2 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p1 p3 p4 p7 p5 p6 : Prop)
theorem file70_51438 : (((((p4 ∨ p5) → (False → False)) → ((p6 → False) ∨ (p2 → p1))) ∨ (((p2 → False) → False) ∧ ((False → p2) ∨ (True ∧ p1)))) → ((((p6 ∧ p2) → (p7 → p7)) ∨ ((p3 → True) → False)) ∨ (((False ∨ p7) → False) → False))) := by
  intro assump_10
  cases assump_10
  case inl assump_11 =>
    apply Or.inl
    apply Or.inl
    intro assump_15
    intro assump_16
    cases assump_15
    case intro assump_19 assump_20 =>
      exact assump_16
  case inr assump_12 =>
    cases assump_12
    case intro assump_25 assump_26 =>
      cases assump_26
      case inl assump_29 =>
        apply Or.inl
        apply Or.inl
        intro assump_33
        intro assump_34
        cases assump_33
        case intro assump_37 assump_38 =>
          exact assump_34
      case inr assump_30 =>
        cases assump_30
        case intro assump_43 assump_44 =>
          apply Or.inl
          apply Or.inl
          intro assump_49
          intro assump_50
          cases assump_49
          case intro assump_53 assump_54 =>
            exact assump_50


variable (p3 p4 p0 p1 p5 : Prop)
theorem file70_52531 : ((((((p5 → p5) ∨ (p0 ∧ p5)) → ((p5 → True) → False)) → (((True → p1) ∧ (p3 → p4)) → ((True → p5) ∧ (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_50 : ((((p5 → p5) ∨ (p0 ∧ p5)) → ((p5 → True) → False)) → (((True → p1) ∧ (p3 → p4)) → ((True → p5) ∧ (p4 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      have assump_51 : ((p5 → p5) ∨ (p0 ∧ p5)) := by
        apply Or.inl
        intro assump_19
        exact assump_19
      let assump_18 := assump_5 assump_51
      have assump_52 : (p5 → True) := by
        intro assump_23
        apply True.intro
      let assump_22 := assump_18 assump_52
      apply False.elim assump_22
    intro assump_27
    cases assump_6
    case intro assump_30 assump_31 =>
      have assump_53 : ((p5 → p5) ∨ (p0 ∧ p5)) := by
        apply Or.inl
        intro assump_39
        exact assump_39
      let assump_38 := assump_5 assump_53
      have assump_54 : (p5 → True) := by
        intro assump_43
        apply True.intro
      let assump_42 := assump_38 assump_54
      apply False.elim assump_42
  let assump_4 := assump_1 assump_50
  apply False.elim assump_4


variable (p0 p2 p3 p5 p7 p4 p1 p6 : Prop)
theorem file70_53827 : (((((False → p7) → False) ∨ ((p6 ∧ p3) ∨ (p0 ∨ p5))) → (((p4 ∨ p1) ∧ (p5 → False)) → ((True → False) → False))) → ((((False ∧ p5) ∧ (p1 ∧ True)) ∧ ((p2 → False) ∨ (False ∧ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p4 p5 p0 p3 p1 : Prop)
theorem file70_54311 : (((((p1 → p5) → False) ∧ ((p1 → False) ∧ (p3 ∧ p5))) ∧ (((p1 ∨ p5) → (p1 ∧ True)) ∧ ((p4 ∧ p3) → (p0 → p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            have assump_39 : (p1 → p5) := by
              intro assump_33
              exact assump_13
            let assump_32 := assump_4 assump_39
            apply False.elim assump_32


variable (p6 p4 p0 p3 p2 p1 p5 : Prop)
theorem file70_55007 : (((((p3 → p6) → (False → False)) ∧ ((p4 → False) → (p5 ∨ p6))) ∧ (((p1 → False) ∧ (p2 → p4)) ∧ ((p1 ∧ p6) ∧ (p5 → False)))) → ((((True ∨ True) → False) → ((p0 ∧ p4) ∧ (p3 ∧ p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_14
          case intro assump_21 assump_22 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              have assump_39 : p1 := by
                exact assump_23
              let assump_35 := assump_15 assump_39
              apply False.elim assump_35


variable (p3 p0 p7 p1 p6 p2 p5 p4 : Prop)
theorem file70_55843 : (((((p4 → p3) → False) ∧ ((p5 → False) ∧ (p4 ∨ p2))) → (((True ∨ p7) ∧ (p3 ∧ p1)) → ((p6 → False) → (p3 → p0)))) ∨ ((((False ∧ True) ∨ (p1 ∨ p0)) → False) ∨ (((p6 ∧ p2) → (p0 ∨ p7)) ∨ ((True ∧ p6) ∨ (p6 → p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_10
      case intro assump_15 assump_16 =>
        cases assump_1
        case intro assump_21 assump_22 =>
          cases assump_22
          case intro assump_25 assump_26 =>
            cases assump_26
            case inl assump_29 =>
              have assump_93 : (p4 → p3) := by
                intro assump_36
                exact assump_15
              let assump_35 := assump_21 assump_93
              apply False.elim assump_35
            case inr assump_30 =>
              have assump_94 : (p4 → p3) := by
                intro assump_47
                exact assump_15
              let assump_46 := assump_21 assump_94
              apply False.elim assump_46
    case inr assump_12 =>
      cases assump_10
      case intro assump_55 assump_56 =>
        cases assump_1
        case intro assump_61 assump_62 =>
          cases assump_62
          case intro assump_65 assump_66 =>
            cases assump_66
            case inl assump_69 =>
              have assump_95 : (p4 → p3) := by
                intro assump_76
                exact assump_55
              let assump_75 := assump_61 assump_95
              apply False.elim assump_75
            case inr assump_70 =>
              have assump_96 : (p4 → p3) := by
                intro assump_87
                exact assump_55
              let assump_86 := assump_61 assump_96
              apply False.elim assump_86


variable (p7 p0 p1 p3 : Prop)
theorem file70_57720 : (((((True → False) ∨ (p0 → False)) ∧ ((True → False) ∧ (p3 → p7))) ∧ (((p3 ∨ p1) → False) ∧ ((p1 → True) ∧ (p7 → p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              have assump_60 : True := by
                apply True.intro
              let assump_30 := assump_10 assump_60
              apply False.elim assump_30
      case inr assump_7 =>
        cases assump_5
        case intro assump_36 assump_37 =>
          cases assump_3
          case intro assump_42 assump_43 =>
            cases assump_43
            case intro assump_46 assump_47 =>
              have assump_61 : True := by
                apply True.intro
              let assump_56 := assump_36 assump_61
              apply False.elim assump_56


variable (p2 p7 p5 p4 p3 p0 p6 : Prop)
theorem file70_58866 : (((((p5 ∧ p3) → False) → False) → (((p0 ∧ p4) → (p0 → p0)) → ((p0 ∨ True) → (p3 → False)))) → ((((True ∧ False) → False) ∨ ((p6 ∧ p2) → False)) ∧ (((False → p5) → False) → ((p5 ∧ p7) → (p7 → p7))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_12
  case intro assump_16 assump_17 =>
    exact assump_17


variable (p1 p3 : Prop)
theorem file70_59395 : ((((((p1 → False) ∨ (p1 → p3)) ∧ ((p3 ∨ True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p1 → False) ∨ (p1 → p3)) ∧ ((p3 ∨ True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_30 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_14 := assump_7 assump_30
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_31 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_22 := assump_7 assump_31
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p5 p6 p4 p1 p0 p2 : Prop)
theorem file70_60207 : (((((True → False) → (p4 → False)) ∧ ((p1 ∧ True) → (False → False))) → False) → ((((p1 ∧ False) → False) ∧ ((p4 ∨ p0) ∨ (p5 ∧ p4))) ∧ (((True → True) → (p0 → p6)) ∨ ((p4 → True) ∧ (p0 ∧ p2))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4
  have assump_58 : (((True → False) → (p4 → False)) ∧ ((p1 ∧ True) → (False → False))) := by
    apply And.intro
    intro assump_12
    intro assump_13
    have assump_59 : True := by
      apply True.intro
    let assump_18 := assump_12 assump_59
    apply False.elim assump_18
    intro assump_22
    intro assump_23
    apply False.elim assump_23
  let assump_11 := assump_1 assump_58
  apply False.elim assump_11
  apply Or.inl
  intro assump_31
  intro assump_32
  have assump_60 : (((True → False) → (p4 → False)) ∧ ((p1 ∧ True) → (False → False))) := by
    apply And.intro
    intro assump_41
    intro assump_42
    have assump_61 : True := by
      apply True.intro
    let assump_47 := assump_41 assump_61
    apply False.elim assump_47
    intro assump_51
    intro assump_52
    apply False.elim assump_52
  let assump_40 := assump_1 assump_60
  apply False.elim assump_40


variable (p3 p1 p0 p6 p4 p7 p2 p5 : Prop)
theorem file70_61512 : (((((p4 ∧ False) ∧ (p7 ∧ p4)) → ((p0 → p6) → (p7 → False))) → False) → ((((p1 → False) ∧ (p5 ∨ p5)) → False) → (((p3 ∧ p3) → (p2 ∧ p4)) ∨ ((p4 → p1) → (p0 ∨ p5))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply And.intro
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_62 : (((p4 ∧ False) ∧ (p7 ∧ p4)) → ((p0 → p6) → (p7 → False))) := by
      intro assump_17
      intro assump_18
      intro assump_19
      cases assump_17
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          apply False.elim assump_27
    let assump_16 := assump_1 assump_62
    apply False.elim assump_16
  cases assump_7
  case intro assump_35 assump_36 =>
    have assump_63 : (((p4 ∧ False) ∧ (p7 ∧ p4)) → ((p0 → p6) → (p7 → False))) := by
      intro assump_44
      intro assump_45
      intro assump_46
      cases assump_44
      case intro assump_51 assump_52 =>
        cases assump_51
        case intro assump_53 assump_54 =>
          apply False.elim assump_54
    let assump_43 := assump_1 assump_63
    apply False.elim assump_43


variable (p6 p1 p7 p3 p0 p4 p5 p2 : Prop)
theorem file70_62711 : (((((p1 → False) ∧ (False ∨ p6)) ∨ ((True ∨ p0) → (True ∧ p6))) ∨ (((True → False) ∨ (p7 ∧ p5)) ∨ ((False ∧ p2) → False))) → ((((p1 ∧ p4) → (False → p7)) ∨ ((p7 → False) → (p3 ∧ p1))) ∧ (((p5 ∨ True) → False) → ((p2 → False) → False)))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          apply Or.inl
          intro assump_16
          intro assump_17
          apply False.elim assump_17
    case inr assump_5 =>
      apply Or.inl
      intro assump_22
      intro assump_23
      apply False.elim assump_23
  case inr assump_3 =>
    cases assump_3
    case inl assump_26 =>
      cases assump_26
      case inl assump_28 =>
        apply Or.inl
        intro assump_32
        intro assump_33
        apply False.elim assump_33
      case inr assump_29 =>
        cases assump_29
        case intro assump_36 assump_37 =>
          apply Or.inl
          intro assump_42
          intro assump_43
          apply False.elim assump_43
    case inr assump_27 =>
      apply Or.inl
      intro assump_48
      intro assump_49
      apply False.elim assump_49
  intro assump_52
  intro assump_53
  cases assump_1
  case inl assump_58 =>
    cases assump_58
    case inl assump_60 =>
      cases assump_60
      case intro assump_62 assump_63 =>
        cases assump_63
        case inl assump_66 =>
          apply False.elim assump_66
        case inr assump_67 =>
          have assump_117 : (p5 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_74 := assump_52 assump_117
          apply False.elim assump_74
    case inr assump_61 =>
      have assump_118 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_84 := assump_52 assump_118
      apply False.elim assump_84
  case inr assump_59 =>
    cases assump_59
    case inl assump_88 =>
      cases assump_88
      case inl assump_90 =>
        have assump_119 : True := by
          apply True.intro
        let assump_94 := assump_90 assump_119
        apply False.elim assump_94
      case inr assump_91 =>
        cases assump_91
        case intro assump_98 assump_99 =>
          have assump_120 : (p5 ∨ True) := by
            apply Or.inl
            exact assump_99
          let assump_106 := assump_52 assump_120
          apply False.elim assump_106
    case inr assump_89 =>
      have assump_121 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_113 := assump_52 assump_121
      apply False.elim assump_113


variable (p3 p6 p0 p2 p7 p5 : Prop)
theorem file70_65515 : ((((((p7 ∧ p6) ∧ (p0 ∧ p7)) ∧ ((p5 ∨ p0) ∨ (False → False))) ∨ (((p3 ∨ False) ∧ (True → False)) → ((p3 ∧ p2) ∨ (p0 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p7 ∧ p6) ∧ (p0 ∧ p7)) ∧ ((p5 ∨ p0) ∨ (False → False))) ∨ (((p3 ∨ False) ∧ (True → False)) → ((p3 ∧ p2) ∨ (p0 ∨ True)))) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inr
        apply Or.inr
        apply True.intro
      case inr assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p4 p3 p2 p7 p0 p6 : Prop)
theorem file70_66226 : (((((True → False) ∧ (p3 ∨ p4)) → False) ∨ (((p4 ∧ p0) → (False ∧ p1)) → False)) ∨ ((((p6 → False) ∧ (p1 ∧ p6)) ∨ ((p2 ∧ p4) → (p4 → False))) → (((p4 ∧ p0) ∧ (p7 ∧ p1)) ∧ ((p6 ∧ p4) ∧ (p0 ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_22 : True := by
        apply True.intro
      let assump_11 := assump_2 assump_22
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_23 : True := by
        apply True.intro
      let assump_18 := assump_2 assump_23
      apply False.elim assump_18


variable (p5 p3 p4 p0 p6 p1 : Prop)
theorem file70_66925 : (((((p3 → False) → (False → p5)) → ((p0 ∧ True) ∧ (p4 → True))) → (((True → False) → (False → False)) ∧ ((True → False) → (True ∧ p5)))) ∨ ((((p6 → False) ∨ (p1 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  apply And.intro
  apply True.intro
  have assump_25 : True := by
    apply True.intro
  let assump_21 := assump_6 assump_25
  apply False.elim assump_21


variable (p4 p6 p7 p1 p5 p2 : Prop)
theorem file70_67465 : ((((((p7 ∨ p4) → (p2 ∨ p6)) → False) → (((p7 ∨ False) ∨ (p6 ∧ p1)) → ((False → p5) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p7 ∨ p4) → (p2 ∨ p6)) → False) → (((p7 ∨ False) ∨ (p6 ∧ p1)) → ((False → p5) ∨ (True → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        intro assump_15
        apply False.elim assump_15
      case inr assump_10 =>
        apply False.elim assump_10
    case inr assump_8 =>
      cases assump_8
      case intro assump_20 assump_21 =>
        apply Or.inl
        intro assump_28
        apply False.elim assump_28
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p2 p4 p3 p5 p1 : Prop)
theorem file70_68296 : (((((p4 → False) → False) → False) ∨ (((p4 → p2) → False) ∧ ((p3 → False) ∧ (p4 ∧ p1)))) → ((((p1 ∧ False) → (p2 ∨ p5)) ∨ ((p1 → p3) ∧ (True → False))) ∨ (((False ∧ p3) → False) ∨ ((p1 ∨ False) → (False → p4))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  case inr assump_3 =>
    cases assump_3
    case intro assump_13 assump_14 =>
      cases assump_14
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          apply Or.inl
          apply Or.inl
          intro assump_27
          cases assump_27
          case intro assump_28 assump_29 =>
            apply False.elim assump_29


variable (p6 p1 p3 p0 p5 p7 p4 : Prop)
theorem file70_69164 : (((((p1 → p3) ∧ (p3 ∨ p5)) → ((True → False) → False)) ∨ (((p4 ∨ p6) ∧ (p5 ∧ True)) → False)) ∨ ((((False → False) ∧ (p1 ∧ p0)) → ((p0 → False) ∧ (False ∧ p0))) ∧ (((p3 → p0) ∨ (False ∨ p4)) ∧ ((p7 → p0) → (p6 ∨ p6))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      have assump_27 : True := by
        apply True.intro
      let assump_15 := assump_2 assump_27
      apply False.elim assump_15
    case inr assump_10 =>
      have assump_28 : True := by
        apply True.intro
      let assump_23 := assump_2 assump_28
      apply False.elim assump_23


variable (p6 p4 p0 p7 p3 : Prop)
theorem file70_69900 : (((((p7 → p7) ∨ (p0 → p4)) ∨ ((p6 → False) ∨ (True → p6))) → False) → ((((p3 ∧ True) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_14 : (((p7 → p7) ∨ (p0 → p4)) ∨ ((p6 → False) ∨ (True → p6))) := by
    apply Or.inl
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p7 p4 p6 p1 p3 p5 p0 p2 : Prop)
theorem file70_70338 : (((((p7 ∨ p6) → (p0 ∧ p3)) ∧ ((p4 → p7) ∨ (p1 → False))) ∧ (((p4 ∨ p5) ∨ (p2 ∨ p5)) ∧ ((p2 ∧ True) → (False ∧ p4)))) → ((((True → p3) → (p1 → p1)) ∨ ((p1 ∨ True) ∨ (True → False))) ∨ (((p0 → p5) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              apply Or.inl
              apply Or.inl
              intro assump_22
              intro assump_23
              exact assump_23
            case inr assump_17 =>
              apply Or.inl
              apply Or.inl
              intro assump_32
              intro assump_33
              exact assump_33
          case inr assump_15 =>
            cases assump_15
            case inl assump_38 =>
              apply Or.inl
              apply Or.inl
              intro assump_44
              intro assump_45
              exact assump_45
            case inr assump_39 =>
              apply Or.inl
              apply Or.inl
              intro assump_54
              intro assump_55
              exact assump_55
      case inr assump_9 =>
        cases assump_3
        case intro assump_62 assump_63 =>
          cases assump_62
          case inl assump_64 =>
            cases assump_64
            case inl assump_66 =>
              apply Or.inl
              apply Or.inl
              intro assump_72
              intro assump_73
              exact assump_73
            case inr assump_67 =>
              apply Or.inl
              apply Or.inl
              intro assump_82
              intro assump_83
              exact assump_83
          case inr assump_65 =>
            cases assump_65
            case inl assump_88 =>
              apply Or.inl
              apply Or.inl
              intro assump_94
              intro assump_95
              exact assump_95
            case inr assump_89 =>
              apply Or.inl
              apply Or.inl
              intro assump_104
              intro assump_105
              exact assump_105


variable (p1 p7 p4 p5 p6 p3 : Prop)
theorem file70_72666 : (((((p7 ∧ p1) → False) → ((p5 → True) ∧ (p6 → True))) ∨ (((True → False) → (True ∨ p4)) → ((p3 ∧ False) ∨ (p4 → True)))) ∨ ((((p3 → p4) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply True.intro
  intro assump_3
  apply True.intro


variable (p4 p5 p1 p3 p0 p7 : Prop)
theorem file70_73033 : ((((((p0 → p3) → (p1 ∨ p1)) ∨ ((p5 → False) ∨ (p7 → False))) → (((p3 ∨ p1) → False) → False)) ∧ ((((p0 → False) → False) ∧ ((p4 ∨ True) ∨ (p3 → False))) ∧ (((p0 → False) → False) ∧ ((True → True) ∧ (False ∧ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  apply False.elim assump_26
          case inr assump_15 =>
            cases assump_7
            case intro assump_32 assump_33 =>
              cases assump_33
              case intro assump_36 assump_37 =>
                cases assump_37
                case intro assump_40 assump_41 =>
                  apply False.elim assump_40
        case inr assump_13 =>
          cases assump_7
          case intro assump_46 assump_47 =>
            cases assump_47
            case intro assump_50 assump_51 =>
              cases assump_51
              case intro assump_54 assump_55 =>
                apply False.elim assump_54


variable (p0 p5 p7 p3 : Prop)
theorem file70_74492 : ((((((True → True) ∨ (False ∨ p5)) ∧ ((p0 → p7) → False)) ∧ (((False → False) → False) ∨ ((p0 → False) ∧ (p7 → False)))) ∧ ((((p3 ∧ False) → (False → p0)) ∨ ((p7 ∨ False) ∨ (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case inl assump_14 =>
            have assump_82 : (((p3 ∧ False) → (False → p0)) ∨ ((p7 ∨ False) ∨ (p3 → False))) := by
              apply Or.inl
              intro assump_21
              intro assump_22
              apply False.elim assump_22
            let assump_20 := assump_3 assump_82
            apply False.elim assump_20
          case inr assump_15 =>
            cases assump_15
            case intro assump_28 assump_29 =>
              have assump_83 : (((p3 ∧ False) → (False → p0)) ∨ ((p7 ∨ False) ∨ (p3 → False))) := by
                apply Or.inl
                intro assump_37
                intro assump_38
                apply False.elim assump_38
              let assump_36 := assump_3 assump_83
              apply False.elim assump_36
        case inr assump_9 =>
          cases assump_9
          case inl assump_44 =>
            apply False.elim assump_44
          case inr assump_45 =>
            cases assump_5
            case inl assump_52 =>
              have assump_84 : (((p3 ∧ False) → (False → p0)) ∨ ((p7 ∨ False) ∨ (p3 → False))) := by
                apply Or.inl
                intro assump_59
                intro assump_60
                apply False.elim assump_60
              let assump_58 := assump_3 assump_84
              apply False.elim assump_58
            case inr assump_53 =>
              cases assump_53
              case intro assump_66 assump_67 =>
                have assump_85 : (((p3 ∧ False) → (False → p0)) ∨ ((p7 ∨ False) ∨ (p3 → False))) := by
                  apply Or.inl
                  intro assump_75
                  intro assump_76
                  apply False.elim assump_76
                let assump_74 := assump_3 assump_85
                apply False.elim assump_74


variable (p4 p2 p5 p1 p6 p0 : Prop)
theorem file70_76804 : (((((p0 → False) → (p2 → False)) → False) → False) → ((((p5 ∧ False) ∧ (p4 → False)) ∧ ((p1 ∧ p5) ∧ (p6 ∨ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8


variable (p1 p5 p4 p0 p7 p2 : Prop)
theorem file70_77225 : ((((((p7 → False) ∧ (True ∧ p0)) → False) ∨ (((p5 → p2) → False) ∨ ((p2 ∧ False) ∧ (p4 ∧ True)))) ∧ ((((p4 ∧ False) ∧ (p0 → False)) → ((False → False) ∧ (p1 ∧ False))) ∧ (((False → False) ∨ (True ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_46 : ((False → False) ∨ (True ∨ True)) := by
          apply Or.inl
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_9 assump_46
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case inl assump_21 =>
        cases assump_3
        case intro assump_25 assump_26 =>
          have assump_47 : ((False → False) ∨ (True ∨ True)) := by
            apply Or.inl
            intro assump_32
            apply False.elim assump_32
          let assump_31 := assump_26 assump_47
          apply False.elim assump_31
      case inr assump_22 =>
        cases assump_22
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            apply False.elim assump_41


variable (p3 p2 p0 p6 p1 : Prop)
theorem file70_78499 : ((((((True → False) ∨ (p0 ∧ p1)) ∨ ((True → p3) ∨ (p3 ∧ p1))) ∧ (((p0 → False) → (p1 ∨ False)) ∧ ((p6 → False) → (True → False)))) ∧ ((((True → p2) → False) → ((p6 → True) ∨ (p0 ∧ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_12 assump_13 =>
            have assump_92 : (((True → p2) → False) → ((p6 → True) ∨ (p0 ∧ p0))) := by
              intro assump_21
              apply Or.inl
              intro assump_24
              apply True.intro
            let assump_20 := assump_3 assump_92
            apply False.elim assump_20
        case inr assump_9 =>
          cases assump_9
          case intro assump_28 assump_29 =>
            cases assump_5
            case intro assump_34 assump_35 =>
              have assump_93 : (((True → p2) → False) → ((p6 → True) ∨ (p0 ∧ p0))) := by
                intro assump_43
                apply Or.inl
                intro assump_46
                apply True.intro
              let assump_42 := assump_3 assump_93
              apply False.elim assump_42
      case inr assump_7 =>
        cases assump_7
        case inl assump_50 =>
          cases assump_5
          case intro assump_54 assump_55 =>
            have assump_94 : (((True → p2) → False) → ((p6 → True) ∨ (p0 ∧ p0))) := by
              intro assump_63
              apply Or.inl
              intro assump_66
              apply True.intro
            let assump_62 := assump_3 assump_94
            apply False.elim assump_62
        case inr assump_51 =>
          cases assump_51
          case intro assump_70 assump_71 =>
            cases assump_5
            case intro assump_76 assump_77 =>
              have assump_95 : (((True → p2) → False) → ((p6 → True) ∨ (p0 ∧ p0))) := by
                intro assump_85
                apply Or.inl
                intro assump_88
                apply True.intro
              let assump_84 := assump_3 assump_95
              apply False.elim assump_84


variable (p1 p7 p5 : Prop)
theorem file70_80742 : ((((((p5 ∨ p7) ∨ (False → p1)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 ∨ p7) ∨ (False → p1)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p5 ∨ p7) ∨ (False → p1)) := by
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p3 p5 p4 p0 p7 p2 : Prop)
theorem file70_81246 : (((((p1 → p5) → (p0 → False)) ∧ ((False ∧ p5) ∧ (p5 → p2))) ∧ (((p5 → False) ∨ (p1 ∨ p1)) ∧ ((False → True) ∨ (False ∧ p4)))) → ((((p3 → False) ∧ (p7 → False)) ∨ ((True → False) ∨ (False ∨ p5))) ∧ (((p7 → False) ∨ (p4 → False)) ∨ ((False ∨ True) → False)))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
  cases assump_1
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          apply False.elim assump_22


variable (p0 p2 p6 p4 p3 p1 : Prop)
theorem file70_82148 : (((((p3 ∨ p6) → (p3 ∧ p3)) ∨ ((p0 ∧ p4) ∧ (True ∨ p1))) → (((False ∧ p2) → False) ∧ ((p1 ∨ p4) ∨ (False ∨ p2)))) → ((((p4 ∧ p0) ∧ (p6 ∧ False)) → False) ∨ (((p2 → p6) ∧ (False → False)) ∨ ((p2 ∧ p1) ∧ (p0 → p4))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case intro assump_13 assump_14 =>
        apply False.elim assump_14


variable (p7 p4 p2 p0 p6 p3 : Prop)
theorem file70_82680 : (((((True ∨ p3) → (True ∧ True)) → False) → (((p2 ∨ p6) → False) ∧ ((p0 ∨ p0) → False))) ∨ ((((p2 ∧ p7) → (p2 ∨ p0)) → False) ∨ (((True → False) → (p4 → False)) ∧ ((p0 → False) ∧ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_44 : ((True ∨ p3) → (True ∧ True)) := by
      intro assump_10
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_9 := assump_1 assump_44
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_45 : ((True ∨ p3) → (True ∧ True)) := by
      intro assump_19
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_18 := assump_1 assump_45
    apply False.elim assump_18
  intro assump_23
  cases assump_23
  case inl assump_24 =>
    have assump_46 : ((True ∨ p3) → (True ∧ True)) := by
      intro assump_31
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_30 := assump_1 assump_46
    apply False.elim assump_30
  case inr assump_25 =>
    have assump_47 : ((True ∨ p3) → (True ∧ True)) := by
      intro assump_40
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_39 := assump_1 assump_47
    apply False.elim assump_39


variable (p2 p7 p3 p0 : Prop)
theorem file70_84020 : (((((p0 ∨ p7) ∨ (False → False)) ∨ ((p2 → p3) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : (((p0 ∨ p7) ∨ (False → False)) ∨ ((p2 → p3) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p4 p3 p6 p2 p7 : Prop)
theorem file70_84404 : (((((p0 ∨ p3) ∧ (p3 ∧ p4)) → ((True ∧ p3) → False)) ∨ (((p7 ∨ p2) ∨ (p0 ∧ p0)) → ((p6 ∧ p2) ∧ (p7 ∨ p7)))) → ((((False → False) → False) → False) ∨ (((p0 ∧ p0) ∧ (p4 ∨ p4)) ∧ ((p7 → p0) ∧ (p4 ∨ p0))))) := by
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    apply Or.inl
    intro assump_19
    have assump_41 : (False → False) := by
      intro assump_23
      apply False.elim assump_23
    let assump_22 := assump_19 assump_41
    apply False.elim assump_22
  case inr assump_16 =>
    apply Or.inl
    intro assump_31
    have assump_42 : (False → False) := by
      intro assump_35
      apply False.elim assump_35
    let assump_34 := assump_31 assump_42
    apply False.elim assump_34


variable (p1 p4 p2 p7 p5 : Prop)
theorem file70_85167 : ((((((p7 ∨ p4) ∧ (p5 ∨ p4)) → False) ∧ (((p5 ∨ p2) ∧ (p4 → p7)) ∨ ((p1 ∧ p7) ∨ (p2 → p4)))) ∧ ((((True ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            have assump_84 : (((True ∨ True) → False) → False) := by
              intro assump_21
              have assump_85 : (True ∨ True) := by
                apply Or.inl
                apply True.intro
              let assump_24 := assump_21 assump_85
              apply False.elim assump_24
            let assump_20 := assump_3 assump_84
            apply False.elim assump_20
          case inr assump_13 =>
            have assump_86 : (((True ∨ True) → False) → False) := by
              intro assump_38
              have assump_87 : (True ∨ True) := by
                apply Or.inl
                apply True.intro
              let assump_41 := assump_38 assump_87
              apply False.elim assump_41
            let assump_37 := assump_3 assump_86
            apply False.elim assump_37
      case inr assump_9 =>
        cases assump_9
        case inl assump_48 =>
          cases assump_48
          case intro assump_50 assump_51 =>
            have assump_88 : (((True ∨ True) → False) → False) := by
              intro assump_59
              have assump_89 : (True ∨ True) := by
                apply Or.inl
                apply True.intro
              let assump_62 := assump_59 assump_89
              apply False.elim assump_62
            let assump_58 := assump_3 assump_88
            apply False.elim assump_58
        case inr assump_49 =>
          have assump_90 : (((True ∨ True) → False) → False) := by
            intro assump_74
            have assump_91 : (True ∨ True) := by
              apply Or.inl
              apply True.intro
            let assump_77 := assump_74 assump_91
            apply False.elim assump_77
          let assump_73 := assump_3 assump_90
          apply False.elim assump_73


variable (p7 p3 p6 p0 p1 p2 : Prop)
theorem file70_87433 : ((((((p6 → False) ∧ (p6 ∧ p1)) → ((False → p7) → False)) → False) ∧ ((((False → False) ∨ (p2 → False)) ∨ ((p3 ∨ True) → False)) ∧ (((p0 ∧ p7) ∨ (p3 ∨ False)) → ((p0 → False) ∧ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_81 : (((p6 → False) ∧ (p6 ∧ p1)) → ((False → p7) → False)) := by
            intro assump_19
            intro assump_20
            cases assump_19
            case intro assump_23 assump_24 =>
              cases assump_24
              case intro assump_27 assump_28 =>
                have assump_82 : p6 := by
                  exact assump_27
                let assump_35 := assump_23 assump_82
                apply False.elim assump_35
          let assump_18 := assump_2 assump_81
          apply False.elim assump_18
        case inr assump_11 =>
          have assump_83 : (((p6 → False) ∧ (p6 ∧ p1)) → ((False → p7) → False)) := by
            intro assump_49
            intro assump_50
            cases assump_49
            case intro assump_53 assump_54 =>
              cases assump_54
              case intro assump_57 assump_58 =>
                have assump_84 : p6 := by
                  exact assump_57
                let assump_65 := assump_53 assump_84
                apply False.elim assump_65
          let assump_48 := assump_2 assump_83
          apply False.elim assump_48
      case inr assump_9 =>
        have assump_85 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_77 := assump_9 assump_85
        apply False.elim assump_77


variable (p7 p2 p4 p3 p1 p0 : Prop)
theorem file70_89254 : (((((p7 → False) → False) → False) → (((p7 ∧ p1) → (True ∨ p1)) → ((False → False) ∨ (p3 ∧ p3)))) ∨ ((((p0 ∧ p4) → (p1 ∧ p2)) → False) → (((p3 → False) → (p4 → False)) → ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p5 p3 p4 p1 p6 p2 p0 : Prop)
theorem file70_89628 : ((((((p2 → p5) ∧ (p2 ∧ p0)) ∨ ((p1 ∧ True) → False)) ∧ (((True → False) → (p1 ∧ p4)) ∨ ((True ∨ p2) ∨ (p3 → False)))) ∧ ((((True ∧ p1) ∨ (False ∨ p2)) → False) ∧ (((p6 ∨ False) ∨ (p1 → False)) ∧ ((p1 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_5
            case inl assump_18 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case inl assump_28 =>
                    cases assump_28
                    case inl assump_30 =>
                      have assump_288 : (p1 → True) := by
                        intro assump_37
                        apply True.intro
                      let assump_36 := assump_27 assump_288
                      apply False.elim assump_36
                    case inr assump_31 =>
                      apply False.elim assump_31
                  case inr assump_29 =>
                    have assump_289 : (p1 → True) := by
                      intro assump_48
                      apply True.intro
                    let assump_47 := assump_27 assump_289
                    apply False.elim assump_47
            case inr assump_19 =>
              cases assump_19
              case inl assump_52 =>
                cases assump_52
                case inl assump_54 =>
                  cases assump_3
                  case intro assump_58 assump_59 =>
                    cases assump_59
                    case intro assump_62 assump_63 =>
                      cases assump_62
                      case inl assump_64 =>
                        cases assump_64
                        case inl assump_66 =>
                          have assump_290 : (p1 → True) := by
                            intro assump_73
                            apply True.intro
                          let assump_72 := assump_63 assump_290
                          apply False.elim assump_72
                        case inr assump_67 =>
                          apply False.elim assump_67
                      case inr assump_65 =>
                        have assump_291 : (p1 → True) := by
                          intro assump_84
                          apply True.intro
                        let assump_83 := assump_63 assump_291
                        apply False.elim assump_83
                case inr assump_55 =>
                  cases assump_3
                  case intro assump_90 assump_91 =>
                    cases assump_91
                    case intro assump_94 assump_95 =>
                      cases assump_94
                      case inl assump_96 =>
                        cases assump_96
                        case inl assump_98 =>
                          have assump_292 : (p1 → True) := by
                            intro assump_105
                            apply True.intro
                          let assump_104 := assump_95 assump_292
                          apply False.elim assump_104
                        case inr assump_99 =>
                          apply False.elim assump_99
                      case inr assump_97 =>
                        have assump_293 : (p1 → True) := by
                          intro assump_116
                          apply True.intro
                        let assump_115 := assump_95 assump_293
                        apply False.elim assump_115
              case inr assump_53 =>
                cases assump_3
                case intro assump_122 assump_123 =>
                  cases assump_123
                  case intro assump_126 assump_127 =>
                    cases assump_126
                    case inl assump_128 =>
                      cases assump_128
                      case inl assump_130 =>
                        have assump_294 : (p1 → True) := by
                          intro assump_137
                          apply True.intro
                        let assump_136 := assump_127 assump_294
                        apply False.elim assump_136
                      case inr assump_131 =>
                        apply False.elim assump_131
                    case inr assump_129 =>
                      have assump_295 : (p1 → True) := by
                        intro assump_148
                        apply True.intro
                      let assump_147 := assump_127 assump_295
                      apply False.elim assump_147
      case inr assump_7 =>
        cases assump_5
        case inl assump_154 =>
          cases assump_3
          case intro assump_158 assump_159 =>
            cases assump_159
            case intro assump_162 assump_163 =>
              cases assump_162
              case inl assump_164 =>
                cases assump_164
                case inl assump_166 =>
                  have assump_296 : (p1 → True) := by
                    intro assump_173
                    apply True.intro
                  let assump_172 := assump_163 assump_296
                  apply False.elim assump_172
                case inr assump_167 =>
                  apply False.elim assump_167
              case inr assump_165 =>
                have assump_297 : (p1 → True) := by
                  intro assump_184
                  apply True.intro
                let assump_183 := assump_163 assump_297
                apply False.elim assump_183
        case inr assump_155 =>
          cases assump_155
          case inl assump_188 =>
            cases assump_188
            case inl assump_190 =>
              cases assump_3
              case intro assump_194 assump_195 =>
                cases assump_195
                case intro assump_198 assump_199 =>
                  cases assump_198
                  case inl assump_200 =>
                    cases assump_200
                    case inl assump_202 =>
                      have assump_298 : (p1 → True) := by
                        intro assump_209
                        apply True.intro
                      let assump_208 := assump_199 assump_298
                      apply False.elim assump_208
                    case inr assump_203 =>
                      apply False.elim assump_203
                  case inr assump_201 =>
                    have assump_299 : (p1 → True) := by
                      intro assump_220
                      apply True.intro
                    let assump_219 := assump_199 assump_299
                    apply False.elim assump_219
            case inr assump_191 =>
              cases assump_3
              case intro assump_226 assump_227 =>
                cases assump_227
                case intro assump_230 assump_231 =>
                  cases assump_230
                  case inl assump_232 =>
                    cases assump_232
                    case inl assump_234 =>
                      have assump_300 : (p1 → True) := by
                        intro assump_241
                        apply True.intro
                      let assump_240 := assump_231 assump_300
                      apply False.elim assump_240
                    case inr assump_235 =>
                      apply False.elim assump_235
                  case inr assump_233 =>
                    have assump_301 : (p1 → True) := by
                      intro assump_252
                      apply True.intro
                    let assump_251 := assump_231 assump_301
                    apply False.elim assump_251
          case inr assump_189 =>
            cases assump_3
            case intro assump_258 assump_259 =>
              cases assump_259
              case intro assump_262 assump_263 =>
                cases assump_262
                case inl assump_264 =>
                  cases assump_264
                  case inl assump_266 =>
                    have assump_302 : (p1 → True) := by
                      intro assump_273
                      apply True.intro
                    let assump_272 := assump_263 assump_302
                    apply False.elim assump_272
                  case inr assump_267 =>
                    apply False.elim assump_267
                case inr assump_265 =>
                  have assump_303 : (p1 → True) := by
                    intro assump_284
                    apply True.intro
                  let assump_283 := assump_263 assump_303
                  apply False.elim assump_283


variable (p4 p0 p3 p6 p1 p7 p2 p5 : Prop)
theorem file70_98455 : (((((p3 → p5) ∨ (p1 ∧ p0)) ∧ ((p4 ∨ p5) → False)) → (((p2 ∧ p4) ∧ (p1 → p7)) ∨ ((p5 ∧ p7) → (p7 ∨ p5)))) ∨ ((((p4 ∧ False) → False) ∨ ((p2 → p4) ∧ (p6 ∨ p7))) ∧ (((p2 ∧ p2) ∧ (p1 → False)) ∨ ((p4 → p2) → (p1 ∨ True))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inr
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply Or.inl
        exact assump_12
    case inr assump_5 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        apply Or.inr
        intro assump_25
        cases assump_25
        case intro assump_26 assump_27 =>
          apply Or.inl
          exact assump_27


variable (p5 p0 p7 p1 p2 : Prop)
theorem file70_99259 : (((((p5 → False) ∨ (p7 ∧ p0)) → ((p5 ∧ False) ∧ (p2 → False))) ∧ (((True → False) ∧ (False ∨ p5)) ∧ ((False → p1) ∨ (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          cases assump_7
          case inl assump_18 =>
            have assump_36 : True := by
              apply True.intro
            let assump_24 := assump_8 assump_36
            apply False.elim assump_24
          case inr assump_19 =>
            have assump_37 : True := by
              apply True.intro
            let assump_32 := assump_8 assump_37
            apply False.elim assump_32


variable (p0 p5 p1 p3 p4 p6 : Prop)
theorem file70_100173 : (((((p1 ∨ p4) → False) → ((False ∧ False) → False)) → False) → ((((p3 ∧ p3) ∨ (p6 ∧ p0)) → ((p1 → True) ∨ (p5 → p6))) → False)) := by
  intro assump_5
  intro assump_6
  have assump_21 : (((p1 ∨ p4) → False) → ((False ∧ False) → False)) := by
    intro assump_12
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
  let assump_11 := assump_5 assump_21
  apply False.elim assump_11


variable (p6 p4 p5 p3 p2 p1 : Prop)
theorem file70_100674 : (((((True → False) ∨ (p6 ∧ p4)) → ((True → False) → (p3 ∨ p2))) ∨ (((p4 ∧ p1) → (p5 ∧ p5)) → ((p1 → False) → (p4 ∨ True)))) → ((((p1 → p3) ∧ (p2 ∨ p1)) ∧ ((True ∧ p5) → False)) → (((False ∨ True) ∨ (p5 ∧ p1)) ∨ ((p2 ∧ True) ∨ (True → p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        cases assump_1
        case inl assump_15 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_16 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_10 =>
        cases assump_1
        case inl assump_25 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_26 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply True.intro


variable (p2 p6 p1 p3 p0 p4 p5 p7 : Prop)
theorem file70_101754 : (((((False ∧ p7) ∧ (p2 ∨ p7)) → ((True → False) → False)) ∨ (((p4 → False) ∨ (p7 → p6)) ∧ ((p5 ∨ True) → (p5 ∧ False)))) ∨ ((((p1 ∨ p7) → (p4 ∨ p1)) → False) ∨ (((p3 → False) ∨ (p3 ∧ p2)) ∨ ((p7 → False) → (p4 ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_7


variable (p0 p5 p7 p4 : Prop)
theorem file70_102236 : ((((((p4 → False) → False) → ((p7 ∨ p0) ∨ (p7 ∨ False))) → False) ∧ ((((p5 ∨ True) → False) → ((p7 → False) ∨ (p0 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p5 ∨ True) → False) → ((p7 → False) ∨ (p0 → False))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      have assump_24 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_16 := assump_9 assump_24
      apply False.elim assump_16
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p2 p6 p0 p1 p5 p3 : Prop)
theorem file70_102890 : ((((((p6 → False) → False) → ((p2 ∧ True) → (p0 → False))) ∧ (((p1 → False) ∧ (False ∨ p5)) ∧ ((True ∨ False) ∧ (False ∧ p3)))) ∧ ((((True → False) → (True → False)) → False) → (((p0 ∧ True) → False) ∧ ((p5 ∨ p2) ∨ (p1 → False))))) → False) := by
  intro assump_46
  cases assump_46
  case intro assump_47 assump_48 =>
    cases assump_47
    case intro assump_49 assump_50 =>
      cases assump_50
      case intro assump_53 assump_54 =>
        cases assump_53
        case intro assump_55 assump_56 =>
          cases assump_56
          case inl assump_59 =>
            apply False.elim assump_59
          case inr assump_60 =>
            cases assump_54
            case intro assump_65 assump_66 =>
              cases assump_65
              case inl assump_67 =>
                cases assump_66
                case intro assump_71 assump_72 =>
                  apply False.elim assump_71
              case inr assump_68 =>
                apply False.elim assump_68


variable (p2 p4 p6 p5 p0 : Prop)
theorem file70_103927 : (((((p4 → p2) → (p2 → p4)) → False) → (((p6 ∧ False) ∨ (p0 → False)) → ((p5 ∧ p4) → False))) ∧ ((((False → True) ∧ (p0 ∧ p6)) → ((p6 → p0) → (p4 → False))) → (((False → True) → False) → False))) := by
  apply And.intro
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_6
    case inl assump_14 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
    case inr assump_15 =>
      have assump_49 : ((p4 → p2) → (p2 → p4)) := by
        intro assump_27
        intro assump_28
        exact assump_9
      let assump_26 := assump_5 assump_49
      apply False.elim assump_26
  intro assump_36
  intro assump_37
  have assump_50 : (False → True) := by
    intro assump_45
    apply True.intro
  let assump_44 := assump_37 assump_50
  apply False.elim assump_44


variable (p3 p7 p5 p2 p1 : Prop)
theorem file70_104857 : ((((((True ∧ False) → False) → False) → (((p2 → p3) ∨ (p1 ∨ p3)) ∧ ((p5 ∨ p2) → (p1 ∨ p7)))) → False) → False) := by
  intro assump_16
  have assump_74 : ((((True ∧ False) → False) → False) → (((p2 → p3) ∨ (p1 ∨ p3)) ∧ ((p5 ∨ p2) → (p1 ∨ p7)))) := by
    intro assump_20
    apply And.intro
    apply Or.inl
    intro assump_23
    have assump_75 : ((True ∧ False) → False) := by
      intro assump_28
      cases assump_28
      case intro assump_29 assump_30 =>
        apply False.elim assump_30
    let assump_27 := assump_20 assump_75
    apply False.elim assump_27
    intro assump_38
    cases assump_38
    case inl assump_39 =>
      have assump_76 : ((True ∧ False) → False) := by
        intro assump_46
        cases assump_46
        case intro assump_47 assump_48 =>
          apply False.elim assump_48
      let assump_45 := assump_20 assump_76
      apply False.elim assump_45
    case inr assump_40 =>
      have assump_77 : ((True ∧ False) → False) := by
        intro assump_61
        cases assump_61
        case intro assump_62 assump_63 =>
          apply False.elim assump_63
      let assump_60 := assump_20 assump_77
      apply False.elim assump_60
  let assump_19 := assump_16 assump_74
  apply False.elim assump_19


variable (p4 p0 p1 p5 p3 p6 : Prop)
theorem file70_106162 : ((((((True ∨ p3) ∨ (p3 ∧ p5)) ∨ ((p1 ∨ p4) ∧ (p4 ∨ p0))) ∨ (((p6 ∧ p0) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ p3) ∨ (p3 ∧ p5)) ∨ ((p1 ∨ p4) ∧ (p4 ∨ p0))) ∨ (((p6 ∧ p0) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p3 p1 p4 p6 p0 p2 : Prop)
theorem file70_106621 : (((((True → False) → (p7 → p3)) ∨ ((p0 ∨ True) → (p2 → p2))) ∧ (((p4 ∨ p6) ∧ (p1 → False)) → ((p1 ∨ p1) → (True → False)))) ∨ ((((p0 → False) ∧ (p2 → True)) → ((p3 → False) ∨ (p1 ∨ p2))) ∨ (((True ∧ p2) → (p1 → False)) → ((p2 ∧ p2) → (p4 ∧ p7))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_62 : True := by
    apply True.intro
  let assump_7 := assump_1 assump_62
  apply False.elim assump_7
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_12
  case inl assump_16 =>
    cases assump_11
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        have assump_63 : p1 := by
          exact assump_16
        let assump_28 := assump_21 assump_63
        apply False.elim assump_28
      case inr assump_23 =>
        have assump_64 : p1 := by
          exact assump_16
        let assump_36 := assump_21 assump_64
        apply False.elim assump_36
  case inr assump_17 =>
    cases assump_11
    case intro assump_42 assump_43 =>
      cases assump_42
      case inl assump_44 =>
        have assump_65 : p1 := by
          exact assump_17
        let assump_50 := assump_43 assump_65
        apply False.elim assump_50
      case inr assump_45 =>
        have assump_66 : p1 := by
          exact assump_17
        let assump_58 := assump_43 assump_66
        apply False.elim assump_58


variable (p6 p3 p7 p2 : Prop)
theorem file70_108079 : (((((p6 → p7) ∧ (p2 ∧ p3)) ∨ ((p7 → False) ∨ (False → p3))) ∧ (((p7 ∨ p7) ∨ (False → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          have assump_49 : ((p7 ∨ p7) ∨ (False → False)) := by
            apply Or.inr
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_3 assump_49
          apply False.elim assump_18
    case inr assump_5 =>
      cases assump_5
      case inl assump_25 =>
        have assump_50 : ((p7 ∨ p7) ∨ (False → False)) := by
          apply Or.inr
          intro assump_32
          apply False.elim assump_32
        let assump_31 := assump_3 assump_50
        apply False.elim assump_31
      case inr assump_26 =>
        have assump_51 : ((p7 ∨ p7) ∨ (False → False)) := by
          apply Or.inr
          intro assump_43
          apply False.elim assump_43
        let assump_42 := assump_3 assump_51
        apply False.elim assump_42


variable (p0 p6 p2 p7 p3 p5 p1 : Prop)
theorem file70_109288 : ((((((p0 → p7) ∧ (p5 ∨ p7)) ∨ ((p6 ∨ p3) → False)) ∧ (((p2 → False) → (p0 → True)) → ((p0 → False) → False))) ∧ ((((False → p7) → False) ∧ ((p6 ∧ p7) → (p5 → False))) ∧ (((p1 ∨ False) ∨ (True ∨ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case inl assump_12 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                have assump_68 : ((p1 ∨ False) ∨ (True ∨ p5)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_28 := assump_19 assump_68
                apply False.elim assump_28
          case inr assump_13 =>
            cases assump_3
            case intro assump_36 assump_37 =>
              cases assump_36
              case intro assump_38 assump_39 =>
                have assump_69 : ((p1 ∨ False) ∨ (True ∨ p5)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_46 := assump_37 assump_69
                apply False.elim assump_46
      case inr assump_7 =>
        cases assump_3
        case intro assump_54 assump_55 =>
          cases assump_54
          case intro assump_56 assump_57 =>
            have assump_70 : ((p1 ∨ False) ∨ (True ∨ p5)) := by
              apply Or.inr
              apply Or.inl
              apply True.intro
            let assump_64 := assump_55 assump_70
            apply False.elim assump_64


variable (p6 p5 p4 p0 p3 p1 p2 : Prop)
theorem file70_111122 : (((((p5 ∨ p4) → (p0 ∧ False)) → ((p0 → True) → False)) ∨ (((p5 ∧ p3) ∨ (p5 ∧ False)) ∧ ((p2 ∨ True) → False))) → ((((False ∧ p5) ∧ (p0 → True)) ∧ ((p4 → p4) ∧ (True ∧ False))) → (((p4 ∧ True) ∧ (False → False)) ∨ ((p6 → p4) → (p2 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


