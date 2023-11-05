variable (p6 p5 p7 p3 p0 p4 p1 : Prop)
theorem file41_47 : (((((p6 ∨ True) ∨ (p7 ∨ p4)) → False) ∧ (((p4 → False) ∨ (p0 → False)) ∧ ((p0 ∧ p3) ∧ (True ∨ p7)))) → ((((p1 ∨ p7) → (p4 ∨ True)) ∧ ((p1 → p0) → False)) ∨ (((False ∧ p4) ∨ (p1 → p7)) → ((p0 ∧ p5) ∧ (True ∨ p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case inl assump_20 =>
              apply Or.inl
              apply And.intro
              intro assump_24
              cases assump_24
              case inl assump_25 =>
                apply Or.inr
                apply True.intro
              case inr assump_26 =>
                apply Or.inr
                apply True.intro
              intro assump_31
              have assump_114 : ((p6 ∨ True) ∨ (p7 ∨ p4)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_38 := assump_2 assump_114
              apply False.elim assump_38
            case inr assump_21 =>
              apply Or.inl
              apply And.intro
              intro assump_44
              cases assump_44
              case inl assump_45 =>
                apply Or.inr
                apply True.intro
              case inr assump_46 =>
                apply Or.inr
                apply True.intro
              intro assump_51
              have assump_115 : ((p6 ∨ True) ∨ (p7 ∨ p4)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_59 := assump_2 assump_115
              apply False.elim assump_59
      case inr assump_9 =>
        cases assump_7
        case intro assump_65 assump_66 =>
          cases assump_65
          case intro assump_67 assump_68 =>
            cases assump_66
            case inl assump_73 =>
              apply Or.inl
              apply And.intro
              intro assump_77
              cases assump_77
              case inl assump_78 =>
                apply Or.inr
                apply True.intro
              case inr assump_79 =>
                apply Or.inr
                apply True.intro
              intro assump_84
              have assump_116 : p0 := by
                exact assump_67
              let assump_90 := assump_9 assump_116
              apply False.elim assump_90
            case inr assump_74 =>
              apply Or.inl
              apply And.intro
              intro assump_96
              cases assump_96
              case inl assump_97 =>
                apply Or.inr
                apply True.intro
              case inr assump_98 =>
                apply Or.inr
                apply True.intro
              intro assump_103
              have assump_117 : p0 := by
                exact assump_67
              let assump_110 := assump_9 assump_117
              apply False.elim assump_110


variable (p1 p7 p6 p3 p4 p5 p0 : Prop)
theorem file41_3190 : (((((p6 → True) → False) → False) → (((False ∧ False) → (p5 ∨ p7)) → False)) → ((((p4 ∧ p1) → (p1 → p1)) → False) ∧ (((p0 → p3) → (p1 ∧ p0)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_48 : (((p6 → True) → False) → False) := by
    intro assump_8
    have assump_49 : (p6 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_8 assump_49
    apply False.elim assump_11
  let assump_7 := assump_1 assump_48
  have assump_50 : ((False ∧ False) → (p5 ∨ p7)) := by
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      apply False.elim assump_18
  let assump_16 := assump_7 assump_50
  apply False.elim assump_16
  intro assump_25
  have assump_51 : (((p6 → True) → False) → False) := by
    intro assump_31
    have assump_52 : (p6 → True) := by
      intro assump_35
      apply True.intro
    let assump_34 := assump_31 assump_52
    apply False.elim assump_34
  let assump_30 := assump_1 assump_51
  have assump_53 : ((False ∧ False) → (p5 ∨ p7)) := by
    intro assump_40
    cases assump_40
    case intro assump_41 assump_42 =>
      apply False.elim assump_41
  let assump_39 := assump_30 assump_53
  apply False.elim assump_39


variable (p3 p7 p2 p5 p4 p6 : Prop)
theorem file41_4484 : ((((((p7 → p3) → False) ∧ ((p3 ∨ p4) ∨ (False ∨ p2))) → (((p4 → False) ∧ (p6 ∧ False)) → False)) → ((((False → p5) → False) → False) → False)) → False) := by
  intro assump_1
  have assump_31 : ((((p7 → p3) → False) ∧ ((p3 ∨ p4) ∨ (False ∨ p2))) → (((p4 → False) ∧ (p6 ∧ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  let assump_4 := assump_1 assump_31
  have assump_32 : (((False → p5) → False) → False) := by
    intro assump_18
    have assump_33 : (False → p5) := by
      intro assump_22
      apply False.elim assump_22
    let assump_21 := assump_18 assump_33
    apply False.elim assump_21
  let assump_17 := assump_4 assump_32
  apply False.elim assump_17


variable (p7 p6 p2 p1 p3 p5 p4 : Prop)
theorem file41_5380 : (((((True ∧ False) ∧ (p3 ∧ p3)) ∨ ((False → p1) ∨ (True ∧ False))) ∨ (((p1 ∧ p1) → (p4 ∧ p6)) ∨ ((p2 → p1) → (p6 → False)))) ∨ ((((p7 ∨ p2) → False) ∨ ((p4 → False) → (True → False))) ∨ (((p5 → False) → False) → ((p5 ∧ True) ∨ (p2 ∧ False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p5 p7 p0 p4 p1 p3 p6 : Prop)
theorem file41_5798 : (((((p4 ∨ p0) ∧ (False → False)) ∨ ((p1 ∧ p3) ∨ (p0 → False))) → False) → ((((p7 → False) ∧ (p5 → p0)) ∨ ((p0 ∨ p5) ∨ (True ∧ p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_85 : (((p4 ∨ p0) ∧ (False → False)) ∨ ((p1 ∧ p3) ∨ (p0 → False))) := by
        apply Or.inr
        apply Or.inr
        intro assump_14
        have assump_86 : (((p4 ∨ p0) ∧ (False → False)) ∨ ((p1 ∧ p3) ∨ (p0 → False))) := by
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_14
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_1 assump_86
        apply False.elim assump_18
      let assump_13 := assump_1 assump_85
      apply False.elim assump_13
  case inr assump_4 =>
    cases assump_4
    case inl assump_28 =>
      cases assump_28
      case inl assump_30 =>
        have assump_87 : (((p4 ∨ p0) ∧ (False → False)) ∨ ((p1 ∧ p3) ∨ (p0 → False))) := by
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_30
          intro assump_37
          apply False.elim assump_37
        let assump_36 := assump_1 assump_87
        apply False.elim assump_36
      case inr assump_31 =>
        have assump_88 : (((p4 ∨ p0) ∧ (False → False)) ∨ ((p1 ∧ p3) ∨ (p0 → False))) := by
          apply Or.inr
          apply Or.inr
          intro assump_48
          have assump_89 : (((p4 ∨ p0) ∧ (False → False)) ∨ ((p1 ∧ p3) ∨ (p0 → False))) := by
            apply Or.inl
            apply And.intro
            apply Or.inr
            exact assump_48
            intro assump_53
            apply False.elim assump_53
          let assump_52 := assump_1 assump_89
          apply False.elim assump_52
        let assump_47 := assump_1 assump_88
        apply False.elim assump_47
    case inr assump_29 =>
      cases assump_29
      case intro assump_62 assump_63 =>
        have assump_90 : (((p4 ∨ p0) ∧ (False → False)) ∨ ((p1 ∧ p3) ∨ (p0 → False))) := by
          apply Or.inr
          apply Or.inr
          intro assump_71
          have assump_91 : (((p4 ∨ p0) ∧ (False → False)) ∨ ((p1 ∧ p3) ∨ (p0 → False))) := by
            apply Or.inl
            apply And.intro
            apply Or.inr
            exact assump_71
            intro assump_76
            apply False.elim assump_76
          let assump_75 := assump_1 assump_91
          apply False.elim assump_75
        let assump_70 := assump_1 assump_90
        apply False.elim assump_70


variable (p7 p5 p1 p4 p3 p2 p6 p0 : Prop)
theorem file41_8456 : (((((p7 → False) ∨ (p5 → p7)) ∧ ((p2 ∧ False) ∧ (p1 → False))) → False) ∨ ((((p0 ∨ False) ∧ (p6 → False)) ∨ ((p4 ∨ p2) → (True ∧ p0))) ∧ (((p1 → p3) → False) → ((p3 → p5) ∨ (p5 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
    case inr assump_5 =>
      cases assump_3
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply False.elim assump_21


variable (p1 p4 p2 p0 : Prop)
theorem file41_9180 : (((((p0 → p1) ∨ (p2 → False)) → ((False → True) ∨ (p4 → p1))) → False) → False) := by
  intro assump_1
  have assump_17 : (((p0 → p1) ∨ (p2 → False)) → ((False → True) ∨ (p4 → p1))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      intro assump_13
      apply True.intro
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p1 p0 p4 : Prop)
theorem file41_9700 : ((((((False ∨ p1) ∨ (p1 → p0)) ∨ ((p4 → False) → False)) ∨ (((p1 → False) → (p1 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False ∨ p1) ∨ (p1 → p0)) ∨ ((p4 → False) → False)) ∨ (((p1 → False) → (p1 → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : ((((False ∨ p1) ∨ (p1 → p0)) ∨ ((p4 → False) → False)) ∨ (((p1 → False) → (p1 → False)) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p6 p3 p7 p5 p4 : Prop)
theorem file41_10450 : (((((True ∨ p4) → False) ∧ ((p4 ∨ False) ∨ (p4 ∧ p3))) → (((p5 → p2) → False) → ((p2 → p6) → False))) ∧ ((((True → False) ∨ (True ∧ p7)) → False) → (((p2 → p2) ∧ (False ∨ True)) ∧ ((p2 → p2) ∨ (p6 ∧ p2))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case inl assump_12 =>
      cases assump_12
      case inl assump_14 =>
        have assump_50 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_19 := assump_8 assump_50
        apply False.elim assump_19
      case inr assump_15 =>
        apply False.elim assump_15
    case inr assump_13 =>
      cases assump_13
      case intro assump_25 assump_26 =>
        have assump_51 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_33 := assump_8 assump_51
        apply False.elim assump_33
  intro assump_37
  apply And.intro
  apply And.intro
  intro assump_38
  exact assump_38
  apply Or.inr
  apply True.intro
  apply Or.inl
  intro assump_47
  exact assump_47


variable (p6 p1 p5 p4 : Prop)
theorem file41_11602 : ((((((False ∨ False) ∧ (True → False)) → ((p4 ∨ p5) → False)) ∨ (((p4 ∧ p6) ∨ (p1 → False)) ∧ ((p4 ∨ p4) → False))) → False) → False) := by
  intro assump_5
  have assump_36 : ((((False ∨ False) ∧ (True → False)) → ((p4 ∨ p5) → False)) ∨ (((p4 ∧ p6) ∨ (p1 → False)) ∧ ((p4 ∨ p4) → False))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_10
    case inl assump_11 =>
      cases assump_9
      case intro assump_15 assump_16 =>
        cases assump_15
        case inl assump_17 =>
          apply False.elim assump_17
        case inr assump_18 =>
          apply False.elim assump_18
    case inr assump_12 =>
      cases assump_9
      case intro assump_25 assump_26 =>
        cases assump_25
        case inl assump_27 =>
          apply False.elim assump_27
        case inr assump_28 =>
          apply False.elim assump_28
  let assump_8 := assump_5 assump_36
  apply False.elim assump_8


variable (p2 p3 p4 : Prop)
theorem file41_12580 : (((((p3 ∧ False) → (p3 ∨ p4)) → ((p2 ∨ p2) → (p3 → p2))) → False) → False) := by
  intro assump_1
  have assump_23 : (((p3 ∧ False) → (p3 ∨ p4)) → ((p2 ∨ p2) → (p3 → p2))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      exact assump_10
    case inr assump_11 =>
      exact assump_11
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p6 p3 p0 p2 p4 p1 : Prop)
theorem file41_13055 : ((((((True ∨ p4) ∨ (p4 → False)) → ((p1 → False) ∨ (p4 ∧ p6))) → (((p2 ∨ p4) ∧ (p2 ∨ p0)) → ((False ∨ True) ∨ (p3 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((True ∨ p4) ∨ (p4 → False)) → ((p1 → False) ∨ (p4 ∧ p6))) → (((p2 ∨ p4) ∧ (p2 ∨ p0)) → ((False ∨ True) ∨ (p3 ∨ p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case inl assump_13 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_14 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_10 =>
        cases assump_8
        case inl assump_25 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_26 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p0 p7 p6 p4 p2 p3 : Prop)
theorem file41_14117 : ((((((p6 → p4) ∧ (True → False)) ∨ ((p2 → False) ∨ (False ∨ False))) ∧ (((p3 → True) → False) → False)) ∧ ((((p0 ∧ True) ∧ (False ∧ p4)) → False) → (((p4 → p7) → (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          have assump_76 : (((p0 ∧ True) ∧ (False ∧ p4)) → False) := by
            intro assump_19
            cases assump_19
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_21
                case intro assump_28 assump_29 =>
                  apply False.elim assump_28
          let assump_18 := assump_3 assump_76
          have assump_77 : ((p4 → p7) → (False → False)) := by
            intro assump_33
            intro assump_34
            apply False.elim assump_34
          let assump_32 := assump_18 assump_77
          apply False.elim assump_32
      case inr assump_7 =>
        cases assump_7
        case inl assump_40 =>
          have assump_78 : (((p0 ∧ True) ∧ (False ∧ p4)) → False) := by
            intro assump_49
            cases assump_49
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_51
                case intro assump_58 assump_59 =>
                  apply False.elim assump_58
          let assump_48 := assump_3 assump_78
          have assump_79 : ((p4 → p7) → (False → False)) := by
            intro assump_63
            intro assump_64
            apply False.elim assump_64
          let assump_62 := assump_48 assump_79
          apply False.elim assump_62
        case inr assump_41 =>
          cases assump_41
          case inl assump_70 =>
            apply False.elim assump_70
          case inr assump_71 =>
            apply False.elim assump_71


variable (p0 p7 p2 p6 p3 p1 p5 p4 : Prop)
theorem file41_16234 : ((((((p4 → False) → False) ∧ ((p6 → p1) → False)) ∨ (((False ∨ False) → (p6 ∧ True)) ∧ ((p6 → False) → (p5 ∧ p4)))) ∧ ((((p2 ∧ p5) → False) → ((p6 ∨ p7) → (True ∧ p3))) ∧ (((p7 ∨ p0) → (False → False)) ∧ ((False → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            have assump_52 : (False → False) := by
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_17 assump_52
            apply False.elim assump_22
    case inr assump_5 =>
      cases assump_5
      case intro assump_29 assump_30 =>
        cases assump_3
        case intro assump_35 assump_36 =>
          cases assump_36
          case intro assump_39 assump_40 =>
            have assump_53 : (False → False) := by
              intro assump_46
              apply False.elim assump_46
            let assump_45 := assump_40 assump_53
            apply False.elim assump_45


variable (p6 p3 p7 p0 p1 p2 p5 : Prop)
theorem file41_17492 : (((((False ∧ p5) ∧ (p0 ∨ p2)) → ((p6 ∨ p6) ∧ (p7 → p7))) ∨ (((p2 ∨ p1) → (p6 → p6)) ∧ ((p1 → False) ∧ (True ∨ p6)))) ∨ ((((p0 → True) ∨ (p1 → False)) → ((p0 ∧ p6) ∨ (p5 ∧ p3))) → (((p1 → p2) → False) ∨ ((p5 ∨ p1) ∧ (p5 → p3))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  apply And.intro
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply False.elim assump_8
  intro assump_12
  cases assump_5
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      apply False.elim assump_17


variable (p2 p3 p5 p1 p0 p7 p4 : Prop)
theorem file41_18155 : (((((p2 ∧ p3) → False) ∧ ((p4 → p7) ∧ (False ∧ p0))) → (((p1 → p0) → (p4 ∨ p4)) → ((p4 ∨ p0) ∧ (p5 ∧ p2)))) ∨ ((((p3 ∧ True) ∧ (p7 ∨ p5)) → False) ∧ (((p1 → p4) → (p3 ∧ p7)) ∧ ((p3 → False) → (p3 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
  apply And.intro
  cases assump_1
  case intro assump_19 assump_20 =>
    cases assump_20
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        apply False.elim assump_27
  cases assump_1
  case intro assump_33 assump_34 =>
    cases assump_34
    case intro assump_37 assump_38 =>
      cases assump_38
      case intro assump_41 assump_42 =>
        apply False.elim assump_41


variable (p1 p6 p7 p0 p4 p5 p2 p3 : Prop)
theorem file41_19140 : (((((p6 → p7) ∨ (p0 → False)) → ((p1 ∨ p1) → False)) ∨ (((p5 ∨ p3) → (p2 → False)) ∨ ((True ∨ p7) ∨ (p7 ∨ p5)))) → ((((p3 → p6) ∧ (True ∧ False)) ∧ ((p2 ∨ p7) ∨ (p0 → p4))) → False)) := by
  intro assump_7
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        apply False.elim assump_16


variable (p7 p5 p1 p2 : Prop)
theorem file41_19623 : (((((p1 → False) ∨ (True ∨ p5)) → ((True → False) → False)) → False) → ((((p2 ∨ False) → (p2 → True)) → False) ∧ (((p7 ∧ False) → False) → ((p7 ∨ p7) ∧ (p5 ∧ p1))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_148 : (((p1 → False) ∨ (True ∨ p5)) → ((True → False) → False)) := by
    intro assump_8
    intro assump_9
    cases assump_8
    case inl assump_12 =>
      have assump_149 : True := by
        apply True.intro
      let assump_17 := assump_9 assump_149
      apply False.elim assump_17
    case inr assump_13 =>
      cases assump_13
      case inl assump_21 =>
        have assump_150 : True := by
          apply True.intro
        let assump_25 := assump_9 assump_150
        apply False.elim assump_25
      case inr assump_22 =>
        have assump_151 : True := by
          apply True.intro
        let assump_32 := assump_9 assump_151
        apply False.elim assump_32
  let assump_7 := assump_1 assump_148
  apply False.elim assump_7
  intro assump_39
  apply And.intro
  have assump_152 : (((p1 → False) ∨ (True ∨ p5)) → ((True → False) → False)) := by
    intro assump_45
    intro assump_46
    cases assump_45
    case inl assump_49 =>
      have assump_153 : True := by
        apply True.intro
      let assump_54 := assump_46 assump_153
      apply False.elim assump_54
    case inr assump_50 =>
      cases assump_50
      case inl assump_58 =>
        have assump_154 : True := by
          apply True.intro
        let assump_62 := assump_46 assump_154
        apply False.elim assump_62
      case inr assump_59 =>
        have assump_155 : True := by
          apply True.intro
        let assump_69 := assump_46 assump_155
        apply False.elim assump_69
  let assump_44 := assump_1 assump_152
  apply False.elim assump_44
  apply And.intro
  have assump_156 : (((p1 → False) ∨ (True ∨ p5)) → ((True → False) → False)) := by
    intro assump_81
    intro assump_82
    cases assump_81
    case inl assump_85 =>
      have assump_157 : True := by
        apply True.intro
      let assump_90 := assump_82 assump_157
      apply False.elim assump_90
    case inr assump_86 =>
      cases assump_86
      case inl assump_94 =>
        have assump_158 : True := by
          apply True.intro
        let assump_98 := assump_82 assump_158
        apply False.elim assump_98
      case inr assump_95 =>
        have assump_159 : True := by
          apply True.intro
        let assump_105 := assump_82 assump_159
        apply False.elim assump_105
  let assump_80 := assump_1 assump_156
  apply False.elim assump_80
  have assump_160 : (((p1 → False) ∨ (True ∨ p5)) → ((True → False) → False)) := by
    intro assump_117
    intro assump_118
    cases assump_117
    case inl assump_121 =>
      have assump_161 : True := by
        apply True.intro
      let assump_126 := assump_118 assump_161
      apply False.elim assump_126
    case inr assump_122 =>
      cases assump_122
      case inl assump_130 =>
        have assump_162 : True := by
          apply True.intro
        let assump_134 := assump_118 assump_162
        apply False.elim assump_134
      case inr assump_131 =>
        have assump_163 : True := by
          apply True.intro
        let assump_141 := assump_118 assump_163
        apply False.elim assump_141
  let assump_116 := assump_1 assump_160
  apply False.elim assump_116


variable (p0 p1 p4 p7 p3 : Prop)
theorem file41_23047 : ((((((False → False) ∨ (p0 ∧ True)) ∧ ((p4 ∨ p7) ∨ (p1 ∧ p1))) ∨ (((p3 ∧ p7) → (p3 → False)) ∨ ((p3 ∨ p3) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((False → False) ∨ (p0 ∧ True)) ∧ ((p4 ∨ p7) ∨ (p1 ∧ p1))) ∨ (((p3 ∧ p7) → (p3 → False)) ∨ ((p3 ∨ p3) ∨ (p0 → False)))) := by
    apply Or.inr
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      have assump_32 : ((((False → False) ∨ (p0 ∧ True)) ∧ ((p4 ∨ p7) ∨ (p1 ∧ p1))) ∨ (((p3 ∧ p7) → (p3 → False)) ∨ ((p3 ∨ p3) ∨ (p0 → False)))) := by
        apply Or.inl
        apply And.intro
        apply Or.inl
        intro assump_22
        apply False.elim assump_22
        apply Or.inl
        apply Or.inr
        exact assump_13
      let assump_21 := assump_1 assump_32
      apply False.elim assump_21
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p4 p6 p3 p2 : Prop)
theorem file41_24024 : (((((False → False) ∨ (p6 → False)) → False) ∧ (((p3 ∧ p3) ∧ (p4 → False)) ∨ ((p3 ∨ p6) ∨ (p2 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_62 : ((False → False) ∨ (p6 → False)) := by
            apply Or.inl
            intro assump_22
            apply False.elim assump_22
          let assump_21 := assump_2 assump_62
          apply False.elim assump_21
    case inr assump_7 =>
      cases assump_7
      case inl assump_28 =>
        cases assump_28
        case inl assump_30 =>
          have assump_63 : ((False → False) ∨ (p6 → False)) := by
            apply Or.inl
            intro assump_36
            apply False.elim assump_36
          let assump_35 := assump_2 assump_63
          apply False.elim assump_35
        case inr assump_31 =>
          have assump_64 : ((False → False) ∨ (p6 → False)) := by
            apply Or.inl
            intro assump_46
            apply False.elim assump_46
          let assump_45 := assump_2 assump_64
          apply False.elim assump_45
      case inr assump_29 =>
        have assump_65 : ((False → False) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_56
          apply False.elim assump_56
        let assump_55 := assump_2 assump_65
        apply False.elim assump_55


variable (p6 p7 p3 p5 p2 p1 p0 p4 : Prop)
theorem file41_25585 : (((((p0 ∨ p6) → False) ∧ ((False → False) ∨ (p0 ∨ p1))) ∧ (((p2 ∧ p0) → (p1 ∨ p1)) → ((False ∧ p4) → (p2 ∧ p7)))) → ((((False → False) ∨ (p4 → False)) ∨ ((True ∨ True) ∨ (p5 ∧ p3))) ∧ (((True → False) → (p1 → p5)) → ((True → True) ∨ (p0 → False))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply Or.inl
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case inl assump_17 =>
          apply Or.inl
          apply Or.inl
          intro assump_23
          apply False.elim assump_23
        case inr assump_18 =>
          apply Or.inl
          apply Or.inl
          intro assump_30
          apply False.elim assump_30
  intro assump_33
  cases assump_1
  case intro assump_36 assump_37 =>
    cases assump_36
    case intro assump_38 assump_39 =>
      cases assump_39
      case inl assump_42 =>
        apply Or.inl
        intro assump_48
        apply True.intro
      case inr assump_43 =>
        cases assump_43
        case inl assump_49 =>
          apply Or.inl
          intro assump_55
          apply True.intro
        case inr assump_50 =>
          apply Or.inl
          intro assump_60
          apply True.intro


variable (p7 p4 p6 p2 p1 p5 p3 : Prop)
theorem file41_27035 : (((((True ∨ p7) ∨ (p5 → False)) ∨ ((p3 → p6) ∧ (p6 → p4))) → False) → ((((p3 → p2) ∨ (True ∧ False)) ∨ ((p5 → False) ∨ (p1 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      have assump_39 : (((True ∨ p7) ∨ (p5 → False)) ∨ ((p3 → p6) ∧ (p6 → p4))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_11 := assump_1 assump_39
      apply False.elim assump_11
    case inr assump_6 =>
      cases assump_6
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
  case inr assump_4 =>
    cases assump_4
    case inl assump_21 =>
      have assump_40 : (((True ∨ p7) ∨ (p5 → False)) ∨ ((p3 → p6) ∧ (p6 → p4))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_27 := assump_1 assump_40
      apply False.elim assump_27
    case inr assump_22 =>
      have assump_41 : (((True ∨ p7) ∨ (p5 → False)) ∨ ((p3 → p6) ∧ (p6 → p4))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_35 := assump_1 assump_41
      apply False.elim assump_35


variable (p5 p7 p0 p3 p6 p1 p2 : Prop)
theorem file41_28328 : ((((((True → False) ∧ (p5 ∨ p6)) → False) ∧ (((True ∨ p0) → (p0 ∨ True)) ∨ ((p5 ∧ p1) → (p3 ∨ p6)))) ∧ ((((p3 → p3) ∨ (p7 ∧ p7)) ∨ ((p2 → False) → (False ∨ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_32 : (((p3 → p3) ∨ (p7 ∧ p7)) ∨ ((p2 → False) → (False ∨ p5))) := by
          apply Or.inl
          apply Or.inl
          intro assump_15
          exact assump_15
        let assump_14 := assump_3 assump_32
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_33 : (((p3 → p3) ∨ (p7 ∧ p7)) ∨ ((p2 → False) → (False ∨ p5))) := by
          apply Or.inl
          apply Or.inl
          intro assump_26
          exact assump_26
        let assump_25 := assump_3 assump_33
        apply False.elim assump_25


variable (p4 p0 p7 p5 p6 p2 : Prop)
theorem file41_29305 : ((((((p0 → False) ∧ (p5 ∧ p6)) ∨ ((p5 → p6) → (True → False))) → (((p4 → False) ∧ (p2 → False)) → ((p7 ∧ p7) → (False → p5)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p0 → False) ∧ (p5 ∧ p6)) ∨ ((p5 → p6) → (True → False))) → (((p4 → False) ∧ (p2 → False)) → ((p7 ∧ p7) → (False → p5)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p2 : Prop)
theorem file41_29842 : (((((p1 ∧ False) ∧ (p2 ∧ True)) → False) → False) → False) := by
  intro assump_5
  have assump_21 : (((p1 ∧ False) ∧ (p2 ∧ True)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
  let assump_8 := assump_5 assump_21
  apply False.elim assump_8


variable (p6 p3 p7 p0 p4 p5 : Prop)
theorem file41_30286 : ((((((True → p7) ∨ (p0 → False)) → False) ∨ (((p4 → p3) → False) → ((p7 → False) → (False ∨ p4)))) ∧ ((((True ∨ p5) → False) → ((False → False) ∨ (p6 ∧ p6))) → False)) → False) := by
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      have assump_39 : (((True ∨ p5) → False) → ((False → False) ∨ (p6 ∧ p6))) := by
        intro assump_16
        apply Or.inl
        intro assump_19
        apply False.elim assump_19
      let assump_15 := assump_8 assump_39
      apply False.elim assump_15
    case inr assump_10 =>
      have assump_40 : (((True ∨ p5) → False) → ((False → False) ∨ (p6 ∧ p6))) := by
        intro assump_30
        apply Or.inl
        intro assump_33
        apply False.elim assump_33
      let assump_29 := assump_8 assump_40
      apply False.elim assump_29


variable (p6 p1 p5 p0 p2 p4 p7 p3 : Prop)
theorem file41_31201 : (((((True ∧ False) ∧ (p4 → False)) → ((False → p0) ∨ (p4 → False))) ∨ (((p1 ∧ p1) → False) → ((p4 → p6) → (p1 → p7)))) ∨ ((((p7 ∧ p6) → (p0 → False)) → False) ∨ (((p3 → False) → (p0 → p5)) ∨ ((p2 → p0) ∨ (False → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_5


variable (p3 p2 p5 p6 p4 p0 p1 : Prop)
theorem file41_31679 : ((((((p6 ∧ p2) → (p1 → False)) ∧ ((p3 ∧ p4) → False)) → (((p4 ∧ p0) ∨ (p1 → False)) ∧ ((p4 ∨ p4) → (p1 → False)))) ∧ ((((p4 → p6) → (p4 ∧ False)) ∨ ((p0 ∨ p1) → (p5 → False))) ∧ (((False → False) ∨ (p4 ∧ p0)) ∧ ((False → False) → False)))) → False) := by
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    cases assump_31
    case intro assump_34 assump_35 =>
      cases assump_34
      case inl assump_36 =>
        cases assump_35
        case intro assump_40 assump_41 =>
          cases assump_40
          case inl assump_42 =>
            have assump_102 : (False → False) := by
              intro assump_49
              apply False.elim assump_49
            let assump_48 := assump_41 assump_102
            apply False.elim assump_48
          case inr assump_43 =>
            cases assump_43
            case intro assump_55 assump_56 =>
              have assump_103 : (False → False) := by
                intro assump_64
                apply False.elim assump_64
              let assump_63 := assump_41 assump_103
              apply False.elim assump_63
      case inr assump_37 =>
        cases assump_35
        case intro assump_72 assump_73 =>
          cases assump_72
          case inl assump_74 =>
            have assump_104 : (False → False) := by
              intro assump_81
              apply False.elim assump_81
            let assump_80 := assump_73 assump_104
            apply False.elim assump_80
          case inr assump_75 =>
            cases assump_75
            case intro assump_87 assump_88 =>
              have assump_105 : (False → False) := by
                intro assump_96
                apply False.elim assump_96
              let assump_95 := assump_73 assump_105
              apply False.elim assump_95


variable (p3 p5 p0 p2 p7 p4 p6 : Prop)
theorem file41_33533 : (((((p2 ∨ False) ∧ (p3 → p7)) → False) ∧ (((p3 ∨ p5) → (p6 ∧ False)) ∨ ((p4 ∨ p6) → (p3 ∨ p0)))) → ((((p2 ∨ p6) ∧ (False ∧ p4)) → False) ∨ (((p0 ∨ p5) → (p4 → p5)) ∧ ((True → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
        case inr assump_14 =>
          cases assump_12
          case intro assump_23 assump_24 =>
            apply False.elim assump_23
    case inr assump_7 =>
      apply Or.inl
      intro assump_29
      cases assump_29
      case intro assump_30 assump_31 =>
        cases assump_30
        case inl assump_32 =>
          cases assump_31
          case intro assump_36 assump_37 =>
            apply False.elim assump_36
        case inr assump_33 =>
          cases assump_31
          case intro assump_42 assump_43 =>
            apply False.elim assump_42


variable (p7 p0 p6 p4 p2 p5 p1 : Prop)
theorem file41_34743 : (((((p4 ∧ p2) → False) ∨ ((True → p0) → (p4 → False))) → (((p4 ∧ p0) ∧ (p6 → False)) → ((p2 → False) → (p2 → False)))) ∨ ((((p6 ∨ p1) ∧ (p7 ∧ p5)) ∧ ((False → False) → (False ∧ p6))) ∧ (((p7 → p6) → False) ∨ ((p6 → p1) ∧ (True → p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_1
      case inl assump_19 =>
        have assump_37 : (p4 ∧ p2) := by
          apply And.intro
          exact assump_11
          exact assump_4
        let assump_23 := assump_19 assump_37
        apply False.elim assump_23
      case inr assump_20 =>
        have assump_38 : (True → p0) := by
          intro assump_30
          exact assump_12
        let assump_29 := assump_20 assump_38
        have assump_39 : p4 := by
          exact assump_11
        let assump_33 := assump_29 assump_39
        apply False.elim assump_33


variable (p5 p7 p2 p0 p1 : Prop)
theorem file41_35790 : (((((p0 ∧ False) → (p7 → p0)) ∨ ((p1 → False) → (True ∧ p0))) → False) → ((((p2 → False) → False) → False) → (((p2 ∨ True) ∧ (p5 → p1)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      have assump_52 : (((p0 ∧ False) → (p7 → p0)) ∨ ((p1 → False) → (True ∧ p0))) := by
        apply Or.inl
        intro assump_17
        intro assump_18
        cases assump_17
        case intro assump_21 assump_22 =>
          apply False.elim assump_22
      let assump_16 := assump_1 assump_52
      apply False.elim assump_16
    case inr assump_7 =>
      have assump_53 : (((p0 ∧ False) → (p7 → p0)) ∨ ((p1 → False) → (True ∧ p0))) := by
        apply Or.inl
        intro assump_39
        intro assump_40
        cases assump_39
        case intro assump_43 assump_44 =>
          apply False.elim assump_44
      let assump_38 := assump_1 assump_53
      apply False.elim assump_38


variable (p2 p1 p5 p3 p6 p4 : Prop)
theorem file41_36846 : ((((((p2 → p1) → (False → False)) ∨ ((p1 → p5) → (p3 ∧ False))) ∨ (((True → p6) → (p1 ∧ p6)) → ((True ∨ p4) ∧ (p4 → p3)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p2 → p1) → (False → False)) ∨ ((p1 → p5) → (p3 ∧ False))) ∨ (((True → p6) → (p1 ∧ p6)) → ((True ∨ p4) ∧ (p4 → p3)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p1 p5 p2 p6 p4 p0 p7 : Prop)
theorem file41_37386 : ((((((p1 → p2) ∨ (p6 ∨ p4)) → ((False → True) → False)) → False) ∧ ((((p5 ∧ p4) ∧ (True → False)) ∧ ((p0 → False) ∨ (True ∧ p4))) ∧ (((p4 → False) ∧ (p0 → False)) ∧ ((p7 → p5) → (p4 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_9
            case inl assump_20 =>
              cases assump_7
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  have assump_66 : (p7 → p5) := by
                    intro assump_35
                    exact assump_12
                  let assump_34 := assump_25 assump_66
                  have assump_67 : p4 := by
                    exact assump_13
                  let assump_38 := assump_34 assump_67
                  apply False.elim assump_38
            case inr assump_21 =>
              cases assump_21
              case intro assump_42 assump_43 =>
                cases assump_7
                case intro assump_48 assump_49 =>
                  cases assump_48
                  case intro assump_50 assump_51 =>
                    have assump_68 : (p7 → p5) := by
                      intro assump_59
                      exact assump_12
                    let assump_58 := assump_49 assump_68
                    have assump_69 : p4 := by
                      exact assump_43
                    let assump_62 := assump_58 assump_69
                    apply False.elim assump_62


variable (p2 p5 p7 p4 p3 p0 p6 : Prop)
theorem file41_39207 : (((((True → p4) ∨ (False → p6)) ∧ ((p6 → False) ∨ (p6 ∨ True))) → (((True → False) → (True ∧ False)) ∨ ((p2 ∧ p3) → False))) ∨ ((((p4 ∧ p6) → (False → False)) → ((p0 → p7) ∧ (p6 → p7))) ∨ (((True ∧ True) → (p4 → False)) → ((p5 ∧ p4) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        apply And.intro
        apply True.intro
        have assump_72 : True := by
          apply True.intro
        let assump_15 := assump_12 assump_72
        apply False.elim assump_15
      case inr assump_9 =>
        cases assump_9
        case inl assump_19 =>
          apply Or.inl
          intro assump_23
          apply And.intro
          apply True.intro
          have assump_73 : True := by
            apply True.intro
          let assump_26 := assump_23 assump_73
          apply False.elim assump_26
        case inr assump_20 =>
          apply Or.inl
          intro assump_32
          apply And.intro
          apply True.intro
          have assump_74 : True := by
            apply True.intro
          let assump_35 := assump_32 assump_74
          apply False.elim assump_35
    case inr assump_5 =>
      cases assump_3
      case inl assump_41 =>
        apply Or.inl
        intro assump_45
        apply And.intro
        apply True.intro
        have assump_75 : True := by
          apply True.intro
        let assump_48 := assump_45 assump_75
        apply False.elim assump_48
      case inr assump_42 =>
        cases assump_42
        case inl assump_52 =>
          apply Or.inl
          intro assump_56
          apply And.intro
          apply True.intro
          have assump_76 : True := by
            apply True.intro
          let assump_59 := assump_56 assump_76
          apply False.elim assump_59
        case inr assump_53 =>
          apply Or.inl
          intro assump_65
          apply And.intro
          apply True.intro
          have assump_77 : True := by
            apply True.intro
          let assump_68 := assump_65 assump_77
          apply False.elim assump_68


variable (p7 p4 p0 p5 p3 p6 : Prop)
theorem file41_41475 : (((((p0 → False) ∧ (p3 ∨ p0)) → ((False → False) ∨ (p7 → p0))) ∨ (((p7 → False) → (False → False)) ∨ ((p3 ∧ p3) ∨ (p4 → False)))) ∨ ((((p4 ∧ p5) ∧ (p0 ∧ p6)) ∨ ((True ∧ p5) → (p6 ∨ p0))) ∨ (((p3 → False) → (True → p4)) → ((p4 → False) → (p3 ∨ p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      apply Or.inl
      intro assump_15
      apply False.elim assump_15


variable (p6 p5 p0 p2 p4 p7 p1 : Prop)
theorem file41_42110 : ((((((p5 ∨ p2) ∨ (p2 ∧ p1)) ∧ ((p2 → p4) ∨ (p1 → p0))) ∧ (((p2 → False) ∧ (p5 → p0)) ∧ ((p7 ∨ p6) ∧ (False ∧ p5)))) ∧ ((((p0 → p5) → (False → False)) → False) ∨ (((p5 ∧ p7) → False) → ((True ∨ True) → (p6 ∨ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_7
            case inl assump_14 =>
              cases assump_5
              case intro assump_18 assump_19 =>
                cases assump_18
                case intro assump_20 assump_21 =>
                  cases assump_19
                  case intro assump_26 assump_27 =>
                    cases assump_26
                    case inl assump_28 =>
                      cases assump_27
                      case intro assump_32 assump_33 =>
                        apply False.elim assump_32
                    case inr assump_29 =>
                      cases assump_27
                      case intro assump_38 assump_39 =>
                        apply False.elim assump_38
            case inr assump_15 =>
              cases assump_5
              case intro assump_44 assump_45 =>
                cases assump_44
                case intro assump_46 assump_47 =>
                  cases assump_45
                  case intro assump_52 assump_53 =>
                    cases assump_52
                    case inl assump_54 =>
                      cases assump_53
                      case intro assump_58 assump_59 =>
                        apply False.elim assump_58
                    case inr assump_55 =>
                      cases assump_53
                      case intro assump_64 assump_65 =>
                        apply False.elim assump_64
          case inr assump_11 =>
            cases assump_7
            case inl assump_70 =>
              cases assump_5
              case intro assump_74 assump_75 =>
                cases assump_74
                case intro assump_76 assump_77 =>
                  cases assump_75
                  case intro assump_82 assump_83 =>
                    cases assump_82
                    case inl assump_84 =>
                      cases assump_83
                      case intro assump_88 assump_89 =>
                        apply False.elim assump_88
                    case inr assump_85 =>
                      cases assump_83
                      case intro assump_94 assump_95 =>
                        apply False.elim assump_94
            case inr assump_71 =>
              cases assump_5
              case intro assump_100 assump_101 =>
                cases assump_100
                case intro assump_102 assump_103 =>
                  cases assump_101
                  case intro assump_108 assump_109 =>
                    cases assump_108
                    case inl assump_110 =>
                      cases assump_109
                      case intro assump_114 assump_115 =>
                        apply False.elim assump_114
                    case inr assump_111 =>
                      cases assump_109
                      case intro assump_120 assump_121 =>
                        apply False.elim assump_120
        case inr assump_9 =>
          cases assump_9
          case intro assump_124 assump_125 =>
            cases assump_7
            case inl assump_130 =>
              cases assump_5
              case intro assump_134 assump_135 =>
                cases assump_134
                case intro assump_136 assump_137 =>
                  cases assump_135
                  case intro assump_142 assump_143 =>
                    cases assump_142
                    case inl assump_144 =>
                      cases assump_143
                      case intro assump_148 assump_149 =>
                        apply False.elim assump_148
                    case inr assump_145 =>
                      cases assump_143
                      case intro assump_154 assump_155 =>
                        apply False.elim assump_154
            case inr assump_131 =>
              cases assump_5
              case intro assump_160 assump_161 =>
                cases assump_160
                case intro assump_162 assump_163 =>
                  cases assump_161
                  case intro assump_168 assump_169 =>
                    cases assump_168
                    case inl assump_170 =>
                      cases assump_169
                      case intro assump_174 assump_175 =>
                        apply False.elim assump_174
                    case inr assump_171 =>
                      cases assump_169
                      case intro assump_180 assump_181 =>
                        apply False.elim assump_180


variable (p2 p7 p3 p6 p4 p5 : Prop)
theorem file41_47097 : (((((p4 → True) → False) ∧ ((p3 ∧ True) ∨ (False ∧ p3))) → False) ∨ ((((p4 ∨ p5) ∨ (p7 ∧ p6)) → ((p5 ∨ p2) ∨ (p7 ∨ False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_24 : (p4 → True) := by
          intro assump_16
          apply True.intro
        let assump_15 := assump_2 assump_24
        apply False.elim assump_15
    case inr assump_7 =>
      cases assump_7
      case intro assump_20 assump_21 =>
        apply False.elim assump_20


variable (p2 p7 p6 : Prop)
theorem file41_47770 : (((((p6 ∨ p2) → (False → False)) ∨ ((p7 → False) ∧ (p6 ∧ False))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p6 ∨ p2) → (False → False)) ∨ ((p7 → False) ∧ (p6 ∧ False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p2 p3 p6 p4 p1 p7 p0 : Prop)
theorem file41_48182 : (((((p0 ∨ True) ∧ (p3 ∨ p1)) ∨ ((p2 ∨ p2) → (p0 → False))) ∧ (((False ∧ p6) → False) ∧ ((p6 → False) ∧ (p0 → False)))) → ((((p3 → False) ∧ (p6 ∧ p3)) ∧ ((p1 ∧ True) → (p4 → False))) → (((False → False) → (True ∨ p7)) ∨ ((p1 ∨ p5) ∧ (p7 ∨ True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_21
              case inl assump_23 =>
                cases assump_22
                case inl assump_27 =>
                  cases assump_18
                  case intro assump_31 assump_32 =>
                    cases assump_32
                    case intro assump_35 assump_36 =>
                      apply Or.inl
                      intro assump_41
                      apply Or.inl
                      apply True.intro
                case inr assump_28 =>
                  cases assump_18
                  case intro assump_46 assump_47 =>
                    cases assump_47
                    case intro assump_50 assump_51 =>
                      apply Or.inl
                      intro assump_56
                      apply Or.inl
                      apply True.intro
              case inr assump_24 =>
                cases assump_22
                case inl assump_61 =>
                  cases assump_18
                  case intro assump_65 assump_66 =>
                    cases assump_66
                    case intro assump_69 assump_70 =>
                      apply Or.inl
                      intro assump_75
                      apply Or.inl
                      apply True.intro
                case inr assump_62 =>
                  cases assump_18
                  case intro assump_80 assump_81 =>
                    cases assump_81
                    case intro assump_84 assump_85 =>
                      apply Or.inl
                      intro assump_90
                      apply Or.inl
                      apply True.intro
          case inr assump_20 =>
            cases assump_18
            case intro assump_95 assump_96 =>
              cases assump_96
              case intro assump_99 assump_100 =>
                apply Or.inl
                intro assump_105
                apply Or.inl
                apply True.intro


variable (p1 p3 p4 p2 : Prop)
theorem file41_50806 : (((((p2 → False) → False) ∨ ((True → False) → False)) ∧ (((p1 → p4) ∨ (p4 ∧ True)) → ((p3 → p3) → (p3 ∧ True)))) → ((((False ∧ p1) ∧ (False → p3)) → False) ∨ (((p3 → False) ∨ (p2 ∨ False)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
    case inr assump_5 =>
      apply Or.inl
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          apply False.elim assump_24


variable (p7 p4 p0 p3 p1 p6 p2 : Prop)
theorem file41_51624 : (((((False ∨ p1) → False) → False) → (((p6 → p6) ∧ (p1 ∨ p1)) ∧ ((p0 ∨ p4) ∧ (p7 → p3)))) → ((((p6 → False) → False) → False) → (((False ∧ p4) → False) ∨ ((p2 → False) ∧ (True ∨ p0))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p1 p7 p5 p2 p0 p4 p3 p6 : Prop)
theorem file41_52029 : (((((p0 ∨ True) ∧ (p4 ∧ p1)) ∧ ((p7 → p0) → (p5 ∧ p3))) ∧ (((p1 ∨ p7) ∨ (p6 → p0)) → False)) → ((((p4 → False) → False) → False) → (((p2 → p3) → (p4 ∨ p6)) ∨ ((True → False) ∨ (p7 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_10
          case intro assump_15 assump_16 =>
            apply Or.inl
            intro assump_25
            apply Or.inl
            exact assump_15
        case inr assump_12 =>
          cases assump_10
          case intro assump_30 assump_31 =>
            apply Or.inl
            intro assump_40
            apply Or.inl
            exact assump_30


variable (p7 p2 p5 p3 p6 p4 : Prop)
theorem file41_52923 : (((((True → p7) ∧ (p4 ∨ p6)) → False) ∧ (((p3 ∧ True) → (p2 ∨ p7)) → False)) → ((((False ∧ p7) ∧ (True → False)) ∧ ((p2 → False) ∨ (False → False))) → (((p3 ∧ p5) → (p4 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply False.elim assump_10


variable (p6 p3 p7 p2 p5 p4 p0 : Prop)
theorem file41_53435 : (((((p0 → p5) ∨ (p6 → False)) ∨ ((False ∧ False) ∨ (p0 ∧ p3))) → (((False → p2) → False) → ((p4 → False) → False))) ∨ ((((p6 → p6) → (p3 ∧ p6)) ∨ ((p6 ∨ p7) → False)) → False)) := by
  apply Or.inl
  intro assump_20
  intro assump_21
  intro assump_22
  cases assump_20
  case inl assump_27 =>
    cases assump_27
    case inl assump_29 =>
      have assump_72 : (False → p2) := by
        intro assump_35
        apply False.elim assump_35
      let assump_34 := assump_21 assump_72
      apply False.elim assump_34
    case inr assump_30 =>
      have assump_73 : (False → p2) := by
        intro assump_45
        apply False.elim assump_45
      let assump_44 := assump_21 assump_73
      apply False.elim assump_44
  case inr assump_28 =>
    cases assump_28
    case inl assump_51 =>
      cases assump_51
      case intro assump_53 assump_54 =>
        apply False.elim assump_53
    case inr assump_52 =>
      cases assump_52
      case intro assump_57 assump_58 =>
        have assump_74 : (False → p2) := by
          intro assump_66
          apply False.elim assump_66
        let assump_65 := assump_21 assump_74
        apply False.elim assump_65


variable (p1 p3 p7 p6 p2 p4 p0 : Prop)
theorem file41_54660 : (((((p2 → False) → (p1 ∧ True)) ∧ ((p6 ∨ p7) ∨ (p2 ∨ p4))) ∧ (((p3 → p3) → False) ∧ ((p1 → False) ∨ (p1 → p3)))) → ((((False ∨ p0) ∨ (True ∧ p0)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_6
          case intro assump_17 assump_18 =>
            cases assump_18
            case inl assump_21 =>
              have assump_129 : (p3 → p3) := by
                intro assump_27
                exact assump_27
              let assump_26 := assump_17 assump_129
              apply False.elim assump_26
            case inr assump_22 =>
              have assump_130 : (p3 → p3) := by
                intro assump_37
                exact assump_37
              let assump_36 := assump_17 assump_130
              apply False.elim assump_36
        case inr assump_14 =>
          cases assump_6
          case intro assump_45 assump_46 =>
            cases assump_46
            case inl assump_49 =>
              have assump_131 : (p3 → p3) := by
                intro assump_55
                exact assump_55
              let assump_54 := assump_45 assump_131
              apply False.elim assump_54
            case inr assump_50 =>
              have assump_132 : (p3 → p3) := by
                intro assump_65
                exact assump_65
              let assump_64 := assump_45 assump_132
              apply False.elim assump_64
      case inr assump_12 =>
        cases assump_12
        case inl assump_71 =>
          cases assump_6
          case intro assump_75 assump_76 =>
            cases assump_76
            case inl assump_79 =>
              have assump_133 : (p3 → p3) := by
                intro assump_85
                exact assump_85
              let assump_84 := assump_75 assump_133
              apply False.elim assump_84
            case inr assump_80 =>
              have assump_134 : (p3 → p3) := by
                intro assump_95
                exact assump_95
              let assump_94 := assump_75 assump_134
              apply False.elim assump_94
        case inr assump_72 =>
          cases assump_6
          case intro assump_103 assump_104 =>
            cases assump_104
            case inl assump_107 =>
              have assump_135 : (p3 → p3) := by
                intro assump_113
                exact assump_113
              let assump_112 := assump_103 assump_135
              apply False.elim assump_112
            case inr assump_108 =>
              have assump_136 : (p3 → p3) := by
                intro assump_123
                exact assump_123
              let assump_122 := assump_103 assump_136
              apply False.elim assump_122


variable (p0 : Prop)
theorem file41_57576 : (((((p0 ∧ p0) ∧ (True → False)) → False) → False) → False) := by
  intro assump_1
  have assump_23 : (((p0 ∧ p0) ∧ (True → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_7 assump_24
        apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p7 p4 p5 p0 p3 : Prop)
theorem file41_58119 : (((((True ∧ p5) ∨ (p7 → False)) ∧ ((True → False) → False)) → False) → ((((p3 ∧ p0) ∧ (True → False)) ∧ ((p4 → False) ∧ (False ∨ p5))) → (((p7 ∨ True) → (p7 → p3)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_7
        case intro assump_18 assump_19 =>
          cases assump_19
          case inl assump_22 =>
            apply False.elim assump_22
          case inr assump_23 =>
            have assump_41 : (((True ∧ p5) ∨ (p7 → False)) ∧ ((True → False) → False)) := by
              apply And.intro
              apply Or.inl
              apply And.intro
              apply True.intro
              exact assump_23
              intro assump_31
              have assump_42 : True := by
                apply True.intro
              let assump_34 := assump_31 assump_42
              apply False.elim assump_34
            let assump_30 := assump_1 assump_41
            apply False.elim assump_30


variable (p0 p5 p4 p6 p1 : Prop)
theorem file41_59294 : (((((p6 ∨ p5) → (True → True)) → False) → (((p0 ∨ p1) ∨ (p4 → False)) ∨ ((False ∧ p5) ∧ (p6 → p4)))) ∨ ((((False → p4) ∨ (p6 ∨ p4)) → False) → False)) := by
  apply Or.inl
  intro assump_5
  apply Or.inl
  apply Or.inr
  intro assump_8
  have assump_18 : ((p6 ∨ p5) → (True → True)) := by
    intro assump_13
    intro assump_14
    apply True.intro
  let assump_12 := assump_5 assump_18
  apply False.elim assump_12


variable (p5 p0 p4 p6 p1 p2 : Prop)
theorem file41_59771 : ((((((p2 → p2) → (p5 → p5)) ∨ ((False → False) ∧ (p1 ∨ p0))) ∨ (((p1 ∧ p4) → False) → ((p2 → False) ∧ (p6 → p2)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 → p2) → (p5 → p5)) ∨ ((False → False) ∧ (p1 ∨ p0))) ∨ (((p1 ∧ p4) → False) → ((p2 → False) ∧ (p6 → p2)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p3 p0 p4 p5 p7 : Prop)
theorem file41_60278 : ((((((True → False) ∨ (p5 → p3)) ∨ ((p0 → p5) → (True ∧ p3))) → False) ∧ ((((p4 ∨ True) ∨ (True ∧ p7)) ∨ ((p4 ∨ p7) → (p0 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (((p4 ∨ True) ∨ (True ∧ p7)) ∨ ((p4 ∨ p7) → (p0 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p3 p7 p1 p0 p4 : Prop)
theorem file41_60796 : (((((False ∨ p4) → False) ∧ ((False ∧ p3) → False)) ∧ (((False → p1) → (p1 → False)) → ((False → False) → False))) → ((((p7 ∧ False) ∧ (False ∨ p4)) → ((False ∧ p0) ∧ (p1 → True))) ∨ (((p1 → p7) ∨ (True ∨ p7)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_12
      apply And.intro
      apply And.intro
      cases assump_12
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
      cases assump_12
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          apply False.elim assump_24
      intro assump_29
      apply True.intro


variable (p7 p3 p5 p2 p1 p0 p4 p6 : Prop)
theorem file41_61672 : ((((((False → p1) ∨ (p3 → p2)) ∨ ((p1 → p2) → (p2 → p5))) → (((False ∧ p4) ∨ (p2 → p7)) → ((p7 → p5) ∨ (p4 → False)))) ∧ ((((p3 ∧ False) → (p6 → False)) ∨ ((p0 → False) → (p6 ∨ p7))) ∧ (((True → True) → (p5 → p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_38 : ((True → True) → (p5 → p5)) := by
          intro assump_15
          intro assump_16
          exact assump_16
        let assump_14 := assump_7 assump_38
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_39 : ((True → True) → (p5 → p5)) := by
          intro assump_29
          intro assump_30
          exact assump_30
        let assump_28 := assump_7 assump_39
        apply False.elim assump_28


variable (p6 p3 p7 : Prop)
theorem file41_62593 : ((((((p3 ∨ True) → False) → False) ∧ (((False → p6) ∨ (False → p7)) ∨ ((False ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 ∨ True) → False) → False) ∧ (((False → p6) ∨ (False → p7)) ∨ ((False ∧ p3) → False))) := by
    apply And.intro
    intro assump_5
    have assump_19 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
    apply Or.inl
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p5 p4 p7 p0 : Prop)
theorem file41_63243 : (((((p7 ∧ False) → False) ∨ ((p4 ∨ p0) ∨ (p5 ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p7 ∧ False) → False) ∨ ((p4 ∨ p0) ∨ (p5 ∧ p6))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 : Prop)
theorem file41_63646 : (((((True ∨ p3) → False) → False) → False) → False) := by
  intro assump_17
  have assump_31 : (((True ∨ p3) → False) → False) := by
    intro assump_21
    have assump_32 : (True ∨ p3) := by
      apply Or.inl
      apply True.intro
    let assump_24 := assump_21 assump_32
    apply False.elim assump_24
  let assump_20 := assump_17 assump_31
  apply False.elim assump_20


variable (p2 : Prop)
theorem file41_64065 : (((((True ∨ p2) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ p2) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ p2) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p4 p2 p3 p1 p6 p7 p0 : Prop)
theorem file41_64497 : (((((p2 ∨ p1) ∧ (p3 ∧ p1)) → ((p0 ∨ True) ∨ (p1 → False))) ∨ (((p2 → p2) → False) ∨ ((False ∨ p6) ∧ (False ∧ p5)))) → ((((p7 ∨ p7) ∨ (p7 → False)) → False) → (((p3 → False) ∧ (p0 → False)) ∧ ((p1 → p2) ∨ (p4 ∨ p4))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    have assump_147 : ((p7 ∨ p7) ∨ (p7 → False)) := by
      apply Or.inr
      intro assump_14
      have assump_148 : ((p7 ∨ p7) ∨ (p7 → False)) := by
        apply Or.inl
        apply Or.inl
        exact assump_14
      let assump_19 := assump_2 assump_148
      apply False.elim assump_19
    let assump_13 := assump_2 assump_147
    apply False.elim assump_13
  case inr assump_9 =>
    cases assump_9
    case inl assump_26 =>
      have assump_149 : (p2 → p2) := by
        intro assump_31
        exact assump_31
      let assump_30 := assump_26 assump_149
      apply False.elim assump_30
    case inr assump_27 =>
      cases assump_27
      case intro assump_37 assump_38 =>
        cases assump_37
        case inl assump_39 =>
          apply False.elim assump_39
        case inr assump_40 =>
          cases assump_38
          case intro assump_45 assump_46 =>
            apply False.elim assump_45
  intro assump_49
  cases assump_1
  case inl assump_54 =>
    have assump_150 : ((p7 ∨ p7) ∨ (p7 → False)) := by
      apply Or.inr
      intro assump_60
      have assump_151 : ((p7 ∨ p7) ∨ (p7 → False)) := by
        apply Or.inl
        apply Or.inl
        exact assump_60
      let assump_65 := assump_2 assump_151
      apply False.elim assump_65
    let assump_59 := assump_2 assump_150
    apply False.elim assump_59
  case inr assump_55 =>
    cases assump_55
    case inl assump_72 =>
      have assump_152 : (p2 → p2) := by
        intro assump_77
        exact assump_77
      let assump_76 := assump_72 assump_152
      apply False.elim assump_76
    case inr assump_73 =>
      cases assump_73
      case intro assump_83 assump_84 =>
        cases assump_83
        case inl assump_85 =>
          apply False.elim assump_85
        case inr assump_86 =>
          cases assump_84
          case intro assump_91 assump_92 =>
            apply False.elim assump_91
  cases assump_1
  case inl assump_97 =>
    apply Or.inl
    intro assump_101
    have assump_153 : ((p7 ∨ p7) ∨ (p7 → False)) := by
      apply Or.inr
      intro assump_107
      have assump_154 : ((p7 ∨ p7) ∨ (p7 → False)) := by
        apply Or.inl
        apply Or.inl
        exact assump_107
      let assump_113 := assump_2 assump_154
      apply False.elim assump_113
    let assump_106 := assump_2 assump_153
    apply False.elim assump_106
  case inr assump_98 =>
    cases assump_98
    case inl assump_120 =>
      apply Or.inl
      intro assump_124
      have assump_155 : (p2 → p2) := by
        intro assump_129
        exact assump_129
      let assump_128 := assump_120 assump_155
      apply False.elim assump_128
    case inr assump_121 =>
      cases assump_121
      case intro assump_135 assump_136 =>
        cases assump_135
        case inl assump_137 =>
          apply False.elim assump_137
        case inr assump_138 =>
          cases assump_136
          case intro assump_143 assump_144 =>
            apply False.elim assump_143


variable (p3 p1 p0 p2 p7 p5 : Prop)
theorem file41_67870 : ((((((False ∧ p3) ∧ (p0 → p7)) ∧ ((False ∨ p5) → (True → False))) → (((p1 → False) → (p2 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ p3) ∧ (p0 → p7)) ∧ ((False ∨ p5) → (True → False))) → (((p1 → False) → (p2 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 p2 p0 p3 p6 p4 p7 : Prop)
theorem file41_68538 : ((((((p6 ∧ p7) → False) → False) → False) ∧ ((((p3 ∨ False) ∧ (False → p2)) ∧ ((p0 ∧ False) ∧ (p4 ∨ p2))) ∨ (((False → False) ∨ (p1 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_9
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_21
          case inr assump_13 =>
            apply False.elim assump_13
    case inr assump_7 =>
      have assump_37 : ((False → False) ∨ (p1 → False)) := by
        apply Or.inl
        intro assump_31
        apply False.elim assump_31
      let assump_30 := assump_7 assump_37
      apply False.elim assump_30


variable (p1 p2 p4 p7 p5 p3 p0 p6 : Prop)
theorem file41_69573 : ((((((p0 ∨ p7) ∧ (False → False)) → False) → (((p4 ∨ p4) ∨ (p6 → False)) ∨ ((p5 ∧ p0) → (p3 → p4)))) ∧ ((((True ∧ p2) ∧ (p0 → True)) → ((p0 → True) ∨ (p1 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((True ∧ p2) ∧ (p0 → True)) → ((p0 → True) ∨ (p1 ∨ p6))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_20
          apply True.intro
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p5 p4 p7 p6 : Prop)
theorem file41_70260 : ((((((p6 → False) → False) → ((p7 ∧ True) ∨ (p7 → False))) → (((p5 ∨ p5) → (False → p5)) ∨ ((p4 → p5) ∨ (p4 → True)))) → False) → False) := by
  intro assump_12
  have assump_26 : ((((p6 → False) → False) → ((p7 ∧ True) ∨ (p7 → False))) → (((p5 ∨ p5) → (False → p5)) ∨ ((p4 → p5) ∨ (p4 → True)))) := by
    intro assump_16
    apply Or.inl
    intro assump_19
    intro assump_20
    apply False.elim assump_20
  let assump_15 := assump_12 assump_26
  apply False.elim assump_15


variable (p1 p6 p5 p4 p7 p0 p2 p3 : Prop)
theorem file41_70805 : ((((((False ∧ p0) → (p0 → p7)) ∨ ((p4 → True) ∧ (p5 ∧ True))) ∨ (((p2 → False) ∨ (False → p4)) → ((p7 → p4) → False))) → ((((p0 ∨ p1) ∧ (p3 ∨ p6)) → ((p4 ∧ False) → False)) → False)) → False) := by
  intro assump_1
  have assump_25 : ((((False ∧ p0) → (p0 → p7)) ∨ ((p4 → True) ∧ (p5 ∧ True))) ∨ (((p2 → False) ∨ (False → p4)) → ((p7 → p4) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_25
  have assump_26 : (((p0 ∨ p1) ∧ (p3 ∨ p6)) → ((p4 ∧ False) → False)) := by
    intro assump_14
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      apply False.elim assump_17
  let assump_13 := assump_4 assump_26
  apply False.elim assump_13


variable (p1 p6 p0 p7 p3 p2 : Prop)
theorem file41_71693 : (((((p6 → False) → (p6 → False)) → False) → (((p7 ∨ p6) → False) → ((p0 → p7) → (p0 → False)))) ∨ ((((p3 → p1) ∧ (True ∧ p6)) ∧ ((p3 → p2) → (p0 ∧ p3))) ∨ (((p0 ∨ True) → False) ∧ ((p1 → p0) ∨ (p1 → p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  have assump_27 : ((p6 → False) → (p6 → False)) := by
    intro assump_14
    intro assump_15
    have assump_28 : p6 := by
      exact assump_15
    let assump_20 := assump_14 assump_28
    apply False.elim assump_20
  let assump_13 := assump_1 assump_27
  apply False.elim assump_13


variable (p7 p1 p5 p6 p4 p3 p2 : Prop)
theorem file41_72338 : (((((p4 ∨ p2) → False) → ((False ∨ p6) ∧ (p2 → p1))) → (((p6 → p2) ∧ (False ∧ p6)) → ((p2 ∧ p7) ∧ (p1 → False)))) ∨ ((((p6 → False) ∧ (p4 ∨ p2)) ∨ ((p3 → False) ∨ (p4 → p5))) ∨ (((False → False) ∨ (p5 ∨ p4)) → ((False ∧ p5) → False)))) := by
  apply Or.inl
  intro assump_4
  intro assump_5
  apply And.intro
  apply And.intro
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  cases assump_5
  case intro assump_14 assump_15 =>
    cases assump_15
    case intro assump_18 assump_19 =>
      apply False.elim assump_18
  intro assump_22
  cases assump_5
  case intro assump_25 assump_26 =>
    cases assump_26
    case intro assump_29 assump_30 =>
      apply False.elim assump_29


variable (p4 p5 p2 p0 p7 : Prop)
theorem file41_73169 : (((((p7 → False) ∧ (True ∨ p2)) ∨ ((p2 → False) ∧ (p7 ∧ p5))) → (((p5 ∧ True) ∨ (p4 → False)) → False)) → ((((p0 ∨ p0) ∨ (False → p7)) ∨ ((False → p5) ∧ (p2 → p7))) → (((p0 → False) → (p4 ∨ p4)) → ((False → True) ∨ (p5 → p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        apply Or.inl
        intro assump_16
        apply True.intro
      case inr assump_11 =>
        apply Or.inl
        intro assump_21
        apply True.intro
    case inr assump_9 =>
      apply Or.inl
      intro assump_26
      apply True.intro
  case inr assump_7 =>
    cases assump_7
    case intro assump_27 assump_28 =>
      apply Or.inl
      intro assump_35
      apply True.intro


variable (p7 p4 p0 p5 p3 p2 p6 : Prop)
theorem file41_74052 : (((((True → p2) ∨ (p7 → False)) ∧ ((p5 ∧ p4) → False)) ∧ (((p5 ∨ False) ∧ (False ∧ False)) ∧ ((p4 ∧ p3) → (p2 ∧ p2)))) → ((((True ∨ p6) ∧ (p0 ∨ p7)) → False) → (((p4 → False) ∨ (p3 ∨ p7)) → False))) := by
  intro assump_12
  intro assump_13
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    cases assump_12
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_23
        case inl assump_25 =>
          cases assump_22
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              cases assump_33
              case inl assump_35 =>
                cases assump_34
                case intro assump_39 assump_40 =>
                  apply False.elim assump_39
              case inr assump_36 =>
                apply False.elim assump_36
        case inr assump_26 =>
          cases assump_22
          case intro assump_49 assump_50 =>
            cases assump_49
            case intro assump_51 assump_52 =>
              cases assump_51
              case inl assump_53 =>
                cases assump_52
                case intro assump_57 assump_58 =>
                  apply False.elim assump_57
              case inr assump_54 =>
                apply False.elim assump_54
  case inr assump_16 =>
    cases assump_16
    case inl assump_63 =>
      cases assump_12
      case intro assump_69 assump_70 =>
        cases assump_69
        case intro assump_71 assump_72 =>
          cases assump_71
          case inl assump_73 =>
            cases assump_70
            case intro assump_79 assump_80 =>
              cases assump_79
              case intro assump_81 assump_82 =>
                cases assump_81
                case inl assump_83 =>
                  cases assump_82
                  case intro assump_87 assump_88 =>
                    apply False.elim assump_87
                case inr assump_84 =>
                  apply False.elim assump_84
          case inr assump_74 =>
            cases assump_70
            case intro assump_97 assump_98 =>
              cases assump_97
              case intro assump_99 assump_100 =>
                cases assump_99
                case inl assump_101 =>
                  cases assump_100
                  case intro assump_105 assump_106 =>
                    apply False.elim assump_105
                case inr assump_102 =>
                  apply False.elim assump_102
    case inr assump_64 =>
      cases assump_12
      case intro assump_115 assump_116 =>
        cases assump_115
        case intro assump_117 assump_118 =>
          cases assump_117
          case inl assump_119 =>
            cases assump_116
            case intro assump_125 assump_126 =>
              cases assump_125
              case intro assump_127 assump_128 =>
                cases assump_127
                case inl assump_129 =>
                  cases assump_128
                  case intro assump_133 assump_134 =>
                    apply False.elim assump_133
                case inr assump_130 =>
                  apply False.elim assump_130
          case inr assump_120 =>
            cases assump_116
            case intro assump_143 assump_144 =>
              cases assump_143
              case intro assump_145 assump_146 =>
                cases assump_145
                case inl assump_147 =>
                  cases assump_146
                  case intro assump_151 assump_152 =>
                    apply False.elim assump_151
                case inr assump_148 =>
                  apply False.elim assump_148


variable (p5 p3 p0 p4 p6 p1 p7 : Prop)
theorem file41_77780 : ((((((p0 ∨ False) → (p6 ∧ p7)) → False) → False) ∧ ((((p6 → False) → False) ∧ ((False → False) ∧ (p6 ∧ False))) ∧ (((p6 ∧ p4) ∧ (p4 ∨ p1)) ∧ ((p0 → p5) → (p3 → False))))) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_26
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_32
        case intro assump_35 assump_36 =>
          cases assump_36
          case intro assump_39 assump_40 =>
            apply False.elim assump_40


variable (p0 p6 p3 p4 p7 p2 p5 : Prop)
theorem file41_78396 : (((((True → False) ∧ (p4 ∧ False)) ∧ ((False ∧ p2) → False)) → (((p0 ∧ p4) → (True → p7)) → ((p4 → p7) → (p6 → p4)))) ∧ ((((p5 → True) ∨ (p3 → False)) → False) → (((p6 ∧ p4) ∨ (p4 ∧ True)) → False))) := by
  apply And.intro
  intro assump_10
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_10
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        apply False.elim assump_27
  intro assump_32
  intro assump_33
  cases assump_33
  case inl assump_34 =>
    cases assump_34
    case intro assump_36 assump_37 =>
      have assump_62 : ((p5 → True) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_45
        apply True.intro
      let assump_44 := assump_32 assump_62
      apply False.elim assump_44
  case inr assump_35 =>
    cases assump_35
    case intro assump_49 assump_50 =>
      have assump_63 : ((p5 → True) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_58
        apply True.intro
      let assump_57 := assump_32 assump_63
      apply False.elim assump_57


variable (p5 : Prop)
theorem file41_79572 : (((((p5 → False) ∧ (True ∧ p5)) → False) → False) → False) := by
  intro assump_1
  have assump_24 : (((p5 → False) ∧ (True ∧ p5)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_25 : p5 := by
          exact assump_11
        let assump_17 := assump_6 assump_25
        apply False.elim assump_17
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p4 p3 p2 p6 p5 p0 : Prop)
theorem file41_80117 : ((((((False ∧ p3) → (p6 ∨ p6)) ∨ ((p0 → False) ∨ (True → p2))) ∨ (((p5 ∨ p6) → (p6 ∨ p0)) ∧ ((False → p4) → False))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p3) → (p6 ∨ p6)) ∨ ((p0 → False) ∨ (True → p2))) ∨ (((p5 ∨ p6) → (p6 ∨ p0)) ∧ ((False → p4) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p1 p5 p4 p6 p3 : Prop)
theorem file41_80677 : (((((False ∧ True) ∧ (p5 → p1)) ∧ ((p1 → p4) ∧ (True → False))) → False) ∧ ((((p6 ∨ True) → False) ∧ ((p3 ∧ True) ∧ (False ∨ p6))) → False)) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        cases assump_16
        case inl assump_23 =>
          apply False.elim assump_23
        case inr assump_24 =>
          have assump_35 : (p6 ∨ True) := by
            apply Or.inl
            exact assump_24
          let assump_31 := assump_11 assump_35
          apply False.elim assump_31


variable (p3 p4 p0 p2 p5 p7 p1 : Prop)
theorem file41_81616 : (((((p2 → False) → False) → ((False → p3) ∨ (p1 → p3))) ∧ (((p0 ∨ True) ∨ (p5 → p2)) → False)) → ((((p1 → False) ∨ (p4 ∧ False)) ∧ ((p7 ∨ p5) → False)) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_5
      case intro assump_15 assump_16 =>
        have assump_31 : ((p0 ∨ True) ∨ (p5 → p2)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_21 := assump_16 assump_31
        apply False.elim assump_21
    case inr assump_10 =>
      cases assump_10
      case intro assump_25 assump_26 =>
        apply False.elim assump_26


variable (p4 p1 p3 p5 p0 p6 : Prop)
theorem file41_82367 : ((((((False ∧ p5) ∧ (p6 → p0)) ∧ ((p4 → p1) → False)) → (((False ∨ False) ∧ (p5 ∨ p1)) → ((True ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((False ∧ p5) ∧ (p6 → p0)) ∧ ((p4 → p1) → False)) → (((False ∨ False) ∧ (p5 ∨ p1)) → ((True ∧ p3) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          apply False.elim assump_16
        case inr assump_17 =>
          apply False.elim assump_17
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p7 p5 p6 p1 : Prop)
theorem file41_83107 : ((((((p1 ∨ p5) ∧ (p1 ∨ True)) ∧ ((p6 → p6) → False)) → (((p7 → p1) ∧ (p7 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_74 : ((((p1 ∨ p5) ∧ (p1 ∨ True)) ∧ ((p6 → p6) → False)) → (((p7 → p1) ∧ (p7 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            cases assump_16
            case inl assump_21 =>
              have assump_75 : (p6 → p6) := by
                intro assump_28
                exact assump_28
              let assump_27 := assump_14 assump_75
              apply False.elim assump_27
            case inr assump_22 =>
              have assump_76 : (p6 → p6) := by
                intro assump_39
                exact assump_39
              let assump_38 := assump_14 assump_76
              apply False.elim assump_38
          case inr assump_18 =>
            cases assump_16
            case inl assump_47 =>
              have assump_77 : (p6 → p6) := by
                intro assump_54
                exact assump_54
              let assump_53 := assump_14 assump_77
              apply False.elim assump_53
            case inr assump_48 =>
              have assump_78 : (p6 → p6) := by
                intro assump_65
                exact assump_65
              let assump_64 := assump_14 assump_78
              apply False.elim assump_64
  let assump_4 := assump_1 assump_74
  apply False.elim assump_4


variable (p6 p1 p3 p5 p0 p7 p4 : Prop)
theorem file41_84799 : (((((p0 ∨ p3) ∧ (p6 ∧ p6)) ∨ ((p4 ∧ p5) → (p0 → p5))) ∧ (((False → p0) ∨ (p6 → False)) ∧ ((p4 ∨ p4) ∨ (p7 ∧ p0)))) ∨ ((((p1 ∧ True) ∧ (p0 → False)) → False) → (((p1 ∧ p7) ∨ (True ∨ p3)) → ((False ∧ p5) → False)))) := by
  apply Or.inr
  intro assump_62
  intro assump_63
  intro assump_64
  cases assump_64
  case intro assump_65 assump_66 =>
    apply False.elim assump_65


variable (p4 p0 p2 p5 p7 : Prop)
theorem file41_85230 : ((((((p0 ∧ p7) ∧ (p5 ∧ p4)) ∧ ((True → False) ∨ (p2 ∨ p0))) ∨ (((p2 → False) → False) → ((False ∨ p7) ∨ (False → False)))) → False) → False) := by
  intro assump_19
  have assump_32 : ((((p0 ∧ p7) ∧ (p5 ∧ p4)) ∧ ((True → False) ∨ (p2 ∨ p0))) ∨ (((p2 → False) → False) → ((False ∨ p7) ∨ (False → False)))) := by
    apply Or.inr
    intro assump_23
    apply Or.inr
    intro assump_26
    apply False.elim assump_26
  let assump_22 := assump_19 assump_32
  apply False.elim assump_22


variable (p3 p2 p4 : Prop)
theorem file41_85765 : ((((((p3 → False) → (p2 → False)) ∧ ((p4 ∨ True) → False)) → False) → False) → False) := by
  intro assump_20
  have assump_38 : ((((p3 → False) → (p2 → False)) ∧ ((p4 ∨ True) → False)) → False) := by
    intro assump_24
    cases assump_24
    case intro assump_25 assump_26 =>
      have assump_39 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_31 := assump_26 assump_39
      apply False.elim assump_31
  let assump_23 := assump_20 assump_38
  apply False.elim assump_23


variable (p6 p5 p2 p4 p7 p1 : Prop)
theorem file41_86335 : ((((((True → False) → (p6 → False)) ∨ ((p4 ∧ p7) → False)) → (((p7 ∨ True) ∨ (p2 ∨ p2)) ∨ ((p5 → False) → (p2 → False)))) → ((((True ∨ False) → (p5 → p5)) → False) ∧ (((True → p2) → (False → False)) ∨ ((p5 ∧ p7) ∨ (p1 ∨ p1))))) → False) := by
  intro assump_1
  have assump_27 : ((((True → False) → (p6 → False)) ∨ ((p4 ∧ p7) → False)) → (((p7 ∨ True) ∨ (p2 ∨ p2)) ∨ ((p5 → False) → (p2 → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_27
  let assump_12 := And.left assump_4
  have assump_28 : ((True ∨ False) → (p5 → p5)) := by
    intro assump_14
    intro assump_15
    cases assump_14
    case inl assump_18 =>
      exact assump_15
    case inr assump_19 =>
      apply False.elim assump_19
  let assump_13 := assump_12 assump_28
  apply False.elim assump_13


variable (p0 p5 p1 p2 p7 p6 p4 : Prop)
theorem file41_87414 : (((((p2 ∧ False) ∧ (p7 → p4)) ∨ ((p5 ∨ p6) ∧ (p1 → False))) ∧ (((p4 ∧ p6) ∧ (p6 ∨ p6)) ∨ ((p2 ∨ p6) ∨ (p4 → p0)))) ∨ ((((p7 ∨ False) ∨ (p2 → True)) ∧ ((p4 ∨ p0) → (p0 ∨ p4))) ∨ (((p1 → p7) → False) → False))) := by
  apply Or.inr
  apply Or.inl
  apply And.intro
  apply Or.inr
  intro assump_1
  apply True.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inr
    exact assump_3
  case inr assump_4 =>
    apply Or.inl
    exact assump_4


variable (p0 p5 p2 p1 p7 p3 p6 : Prop)
theorem file41_87943 : (((((p2 → p3) → False) → ((p3 ∧ p0) ∨ (p1 → False))) → (((p0 → False) ∧ (p5 → False)) ∧ ((p5 → p1) → False))) → ((((p2 ∨ False) ∧ (p3 ∧ True)) ∧ ((p7 → p6) → False)) → (((p0 → p0) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          have assump_75 : (((p2 → p3) → False) → ((p3 ∧ p0) ∨ (p1 → False))) := by
            intro assump_25
            apply Or.inr
            intro assump_28
            have assump_76 : (p2 → p3) := by
              intro assump_33
              exact assump_14
            let assump_32 := assump_25 assump_76
            apply False.elim assump_32
          let assump_24 := assump_1 assump_75
          let assump_39 := And.right assump_24
          have assump_77 : (p5 → p1) := by
            intro assump_44
            have assump_78 : (((p2 → p3) → False) → ((p3 ∧ p0) ∨ (p1 → False))) := by
              intro assump_49
              apply Or.inr
              intro assump_52
              have assump_79 : (p2 → p3) := by
                intro assump_57
                exact assump_14
              let assump_56 := assump_49 assump_79
              apply False.elim assump_56
            let assump_48 := assump_1 assump_78
            let assump_63 := And.left assump_48
            let assump_64 := And.right assump_63
            have assump_80 : p5 := by
              exact assump_44
            let assump_66 := assump_64 assump_80
            apply False.elim assump_66
          let assump_43 := assump_39 assump_77
          apply False.elim assump_43
      case inr assump_11 =>
        apply False.elim assump_11


variable (p3 p5 p4 p2 p1 p6 p7 p0 : Prop)
theorem file41_89832 : (((((p5 → False) → (p2 → p6)) ∧ ((p3 → False) → False)) → (((p4 → False) → (p7 ∨ True)) → ((p6 → p6) ∨ (p7 → False)))) ∨ ((((p3 ∧ p3) ∨ (p4 ∧ p0)) → ((True → p5) → (p1 → False))) ∨ (((p7 → False) → False) → False))) := by
  apply Or.inl
  intro assump_7
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    apply Or.inl
    intro assump_17
    exact assump_17


variable (p6 p5 p7 p1 p0 p4 : Prop)
theorem file41_90273 : ((((((True ∨ p1) → False) ∧ ((p0 ∧ p5) → (p1 → p1))) → (((p7 ∨ p6) ∧ (p4 → False)) ∧ ((True → p1) ∨ (p7 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_48 : ((((True ∨ p1) → False) ∧ ((p0 ∧ p5) → (p1 → p1))) → (((p7 ∨ p6) ∧ (p4 → False)) ∧ ((True → p1) ∨ (p7 ∨ p6)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_49 : (True ∨ p1) := by
        apply Or.inl
        apply True.intro
      let assump_13 := assump_6 assump_49
      apply False.elim assump_13
    intro assump_17
    cases assump_5
    case intro assump_20 assump_21 =>
      have assump_50 : (True ∨ p1) := by
        apply Or.inl
        apply True.intro
      let assump_27 := assump_20 assump_50
      apply False.elim assump_27
    cases assump_5
    case intro assump_31 assump_32 =>
      apply Or.inl
      intro assump_37
      have assump_51 : (True ∨ p1) := by
        apply Or.inl
        apply True.intro
      let assump_41 := assump_31 assump_51
      apply False.elim assump_41
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p6 p4 p7 p1 p0 : Prop)
theorem file41_91462 : ((((((False → p4) → False) → ((p6 → p1) → False)) ∨ (((False ∨ p7) → False) ∧ ((False ∧ p4) ∨ (p0 → False)))) → False) → False) := by
  intro assump_5
  have assump_25 : ((((False → p4) → False) → ((p6 → p1) → False)) ∨ (((False ∨ p7) → False) ∧ ((False ∧ p4) ∨ (p0 → False)))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    have assump_26 : (False → p4) := by
      intro assump_16
      apply False.elim assump_16
    let assump_15 := assump_9 assump_26
    apply False.elim assump_15
  let assump_8 := assump_5 assump_25
  apply False.elim assump_8


variable (p3 p0 p6 p4 p1 : Prop)
theorem file41_92090 : (((((True ∨ p6) ∨ (p1 ∧ p3)) ∧ ((p0 ∧ p4) ∧ (False ∨ True))) ∧ (((p1 ∧ False) ∨ (True → True)) → ((p4 → False) ∧ (p3 → False)))) → False) := by
  intro assump_260
  cases assump_260
  case intro assump_261 assump_262 =>
    cases assump_261
    case intro assump_263 assump_264 =>
      cases assump_263
      case inl assump_265 =>
        cases assump_265
        case inl assump_267 =>
          cases assump_264
          case intro assump_271 assump_272 =>
            cases assump_271
            case intro assump_273 assump_274 =>
              cases assump_272
              case inl assump_279 =>
                apply False.elim assump_279
              case inr assump_280 =>
                have assump_348 : ((p1 ∧ False) ∨ (True → True)) := by
                  apply Or.inr
                  intro assump_288
                  apply True.intro
                let assump_287 := assump_262 assump_348
                let assump_289 := And.left assump_287
                have assump_349 : p4 := by
                  exact assump_274
                let assump_290 := assump_289 assump_349
                apply False.elim assump_290
        case inr assump_268 =>
          cases assump_264
          case intro assump_296 assump_297 =>
            cases assump_296
            case intro assump_298 assump_299 =>
              cases assump_297
              case inl assump_304 =>
                apply False.elim assump_304
              case inr assump_305 =>
                have assump_350 : ((p1 ∧ False) ∨ (True → True)) := by
                  apply Or.inr
                  intro assump_313
                  apply True.intro
                let assump_312 := assump_262 assump_350
                let assump_314 := And.left assump_312
                have assump_351 : p4 := by
                  exact assump_299
                let assump_315 := assump_314 assump_351
                apply False.elim assump_315
      case inr assump_266 =>
        cases assump_266
        case intro assump_319 assump_320 =>
          cases assump_264
          case intro assump_325 assump_326 =>
            cases assump_325
            case intro assump_327 assump_328 =>
              cases assump_326
              case inl assump_333 =>
                apply False.elim assump_333
              case inr assump_334 =>
                have assump_352 : ((p1 ∧ False) ∨ (True → True)) := by
                  apply Or.inr
                  intro assump_342
                  apply True.intro
                let assump_341 := assump_262 assump_352
                let assump_343 := And.left assump_341
                have assump_353 : p4 := by
                  exact assump_328
                let assump_344 := assump_343 assump_353
                apply False.elim assump_344


variable (p3 p1 p6 p4 p5 p0 : Prop)
theorem file41_94945 : (((((p4 → False) → (p1 ∨ True)) → ((False → False) → False)) → (((p6 ∧ False) → False) → False)) ∧ ((((True → p0) ∨ (p3 → False)) → False) → (((p6 → True) ∨ (p4 ∨ p6)) ∧ ((p0 ∨ p5) → (p0 → False))))) := by
  apply And.intro
  intro assump_8
  intro assump_9
  have assump_57 : ((p4 → False) → (p1 ∨ True)) := by
    intro assump_15
    apply Or.inr
    apply True.intro
  let assump_14 := assump_8 assump_57
  have assump_58 : (False → False) := by
    intro assump_19
    apply False.elim assump_19
  let assump_18 := assump_14 assump_58
  apply False.elim assump_18
  intro assump_25
  apply And.intro
  apply Or.inl
  intro assump_28
  apply True.intro
  intro assump_29
  intro assump_30
  cases assump_29
  case inl assump_33 =>
    have assump_59 : ((True → p0) ∨ (p3 → False)) := by
      apply Or.inl
      intro assump_40
      exact assump_33
    let assump_39 := assump_25 assump_59
    apply False.elim assump_39
  case inr assump_34 =>
    have assump_60 : ((True → p0) ∨ (p3 → False)) := by
      apply Or.inl
      intro assump_51
      exact assump_30
    let assump_50 := assump_25 assump_60
    apply False.elim assump_50


variable (p6 p1 p0 p7 p2 p3 : Prop)
theorem file41_96145 : ((((((False → False) ∨ (False → False)) → False) ∨ (((p1 ∧ p2) → (p3 ∨ False)) → ((p7 → False) ∧ (p1 → False)))) ∧ ((((p0 → False) → False) → ((p6 ∧ p3) ∧ (p7 → False))) ∧ (((False ∧ p6) → (p2 → p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_46 : ((False ∧ p6) → (p2 → p2)) := by
          intro assump_15
          intro assump_16
          cases assump_15
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
        let assump_14 := assump_9 assump_46
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_3
      case intro assump_28 assump_29 =>
        have assump_47 : ((False ∧ p6) → (p2 → p2)) := by
          intro assump_35
          intro assump_36
          cases assump_35
          case intro assump_39 assump_40 =>
            apply False.elim assump_39
        let assump_34 := assump_29 assump_47
        apply False.elim assump_34


variable (p5 p7 p0 p6 : Prop)
theorem file41_97279 : ((((((p0 ∨ p7) ∨ (p6 → False)) ∨ ((p5 → False) → (p5 → False))) → False) ∧ ((((p6 ∧ False) ∧ (False ∨ True)) → ((p5 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p6 ∧ False) ∧ (False ∨ True)) → ((p5 → False) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p4 p1 p6 p0 p3 p2 : Prop)
theorem file41_97929 : (((((False ∨ p6) → False) ∧ ((False → False) → False)) ∧ (((p2 ∧ p6) → False) ∧ ((p4 → False) ∧ (p0 → p0)))) → ((((p1 ∧ p6) ∧ (p4 → p6)) → False) ∨ (((False ∧ p4) ∧ (p3 → False)) ∨ ((True ∧ p6) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply Or.inl
          intro assump_20
          cases assump_20
          case intro assump_21 assump_22 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              have assump_44 : (False → False) := by
                intro assump_38
                apply False.elim assump_38
              let assump_37 := assump_5 assump_44
              apply False.elim assump_37


variable (p2 p1 p0 p7 p6 p4 p3 : Prop)
theorem file41_98866 : (((((p1 ∨ True) → (p1 ∧ False)) ∨ ((p4 → False) → False)) → (((False → False) ∨ (p6 ∧ p0)) ∧ ((p7 ∨ p0) ∨ (False → True)))) ∨ ((((False → False) → (True → False)) ∧ ((True ∨ p4) ∨ (False → False))) → (((p2 ∨ p7) → (p3 ∧ True)) → ((True → False) ∧ (p1 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    apply Or.inl
    intro assump_11
    apply False.elim assump_11
  cases assump_1
  case inl assump_14 =>
    apply Or.inr
    intro assump_18
    apply True.intro
  case inr assump_15 =>
    apply Or.inr
    intro assump_21
    apply True.intro


variable (p6 p0 p7 : Prop)
theorem file41_99612 : ((((((True ∧ False) ∧ (False ∨ False)) → False) ∨ (((p0 → False) → (p7 ∨ p7)) ∨ ((p6 ∨ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((True ∧ False) ∧ (False ∨ False)) → False) ∨ (((p0 → False) → (p7 ∨ p7)) ∨ ((p6 ∨ p6) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p1 p7 p5 p2 p4 : Prop)
theorem file41_100186 : (((((True ∨ p4) ∨ (p2 → False)) → False) → False) → ((((p5 ∧ p4) ∨ (False → p1)) ∨ ((p7 ∧ True) → (p5 ∨ p5))) ∨ (((p2 → p4) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


variable (p3 p6 p0 p5 p1 p7 : Prop)
theorem file41_100503 : (((((False → False) ∨ (p0 → False)) ∨ ((True ∧ p3) → False)) → False) → ((((p6 ∧ p7) → (p1 ∨ p7)) → False) ∧ (((p6 → False) → (False → False)) → ((True ∨ p5) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_44 : (((False → False) ∨ (p0 → False)) ∨ ((True ∧ p3) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_44
  apply False.elim assump_7
  intro assump_14
  intro assump_15
  cases assump_15
  case inl assump_16 =>
    have assump_45 : (((False → False) ∨ (p0 → False)) ∨ ((True ∧ p3) → False)) := by
      apply Or.inl
      apply Or.inl
      intro assump_25
      apply False.elim assump_25
    let assump_24 := assump_1 assump_45
    apply False.elim assump_24
  case inr assump_17 =>
    have assump_46 : (((False → False) ∨ (p0 → False)) ∨ ((True ∧ p3) → False)) := by
      apply Or.inl
      apply Or.inl
      intro assump_38
      apply False.elim assump_38
    let assump_37 := assump_1 assump_46
    apply False.elim assump_37


variable (p7 p2 p6 p3 p0 p5 : Prop)
theorem file41_101625 : (((((p3 → False) ∨ (p6 ∨ p0)) ∧ ((p7 ∨ p0) ∨ (False ∧ False))) ∨ (((p7 ∧ p3) ∧ (p5 ∧ p0)) ∨ ((p6 → True) ∧ (p7 → p7)))) → ((((p2 ∨ p2) → False) ∧ ((p3 ∨ p0) → False)) → (((False ∧ p5) ∨ (True ∧ p3)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  case inr assump_5 =>
    cases assump_5
    case intro assump_10 assump_11 =>
      cases assump_2
      case intro assump_16 assump_17 =>
        cases assump_1
        case inl assump_22 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            cases assump_24
            case inl assump_26 =>
              cases assump_25
              case inl assump_30 =>
                cases assump_30
                case inl assump_32 =>
                  have assump_142 : p3 := by
                    exact assump_11
                  let assump_37 := assump_26 assump_142
                  apply False.elim assump_37
                case inr assump_33 =>
                  have assump_143 : p3 := by
                    exact assump_11
                  let assump_44 := assump_26 assump_143
                  apply False.elim assump_44
              case inr assump_31 =>
                cases assump_31
                case intro assump_48 assump_49 =>
                  apply False.elim assump_48
            case inr assump_27 =>
              cases assump_27
              case inl assump_52 =>
                cases assump_25
                case inl assump_56 =>
                  cases assump_56
                  case inl assump_58 =>
                    have assump_144 : (p3 ∨ p0) := by
                      apply Or.inl
                      exact assump_11
                    let assump_64 := assump_17 assump_144
                    apply False.elim assump_64
                  case inr assump_59 =>
                    have assump_145 : (p3 ∨ p0) := by
                      apply Or.inl
                      exact assump_11
                    let assump_72 := assump_17 assump_145
                    apply False.elim assump_72
                case inr assump_57 =>
                  cases assump_57
                  case intro assump_76 assump_77 =>
                    apply False.elim assump_76
              case inr assump_53 =>
                cases assump_25
                case inl assump_82 =>
                  cases assump_82
                  case inl assump_84 =>
                    have assump_146 : (p3 ∨ p0) := by
                      apply Or.inl
                      exact assump_11
                    let assump_90 := assump_17 assump_146
                    apply False.elim assump_90
                  case inr assump_85 =>
                    have assump_147 : (p3 ∨ p0) := by
                      apply Or.inl
                      exact assump_11
                    let assump_98 := assump_17 assump_147
                    apply False.elim assump_98
                case inr assump_83 =>
                  cases assump_83
                  case intro assump_102 assump_103 =>
                    apply False.elim assump_102
        case inr assump_23 =>
          cases assump_23
          case inl assump_106 =>
            cases assump_106
            case intro assump_108 assump_109 =>
              cases assump_108
              case intro assump_110 assump_111 =>
                cases assump_109
                case intro assump_116 assump_117 =>
                  have assump_148 : (p3 ∨ p0) := by
                    apply Or.inl
                    exact assump_111
                  let assump_126 := assump_17 assump_148
                  apply False.elim assump_126
          case inr assump_107 =>
            cases assump_107
            case intro assump_130 assump_131 =>
              have assump_149 : (p3 ∨ p0) := by
                apply Or.inl
                exact assump_11
              let assump_138 := assump_17 assump_149
              apply False.elim assump_138


variable (p1 p4 p7 p3 p5 p2 : Prop)
theorem file41_105754 : (((((p4 → False) → False) ∨ ((True ∧ p1) ∨ (p1 ∧ p2))) → False) → ((((False ∧ p4) → False) ∨ ((p5 → True) ∧ (p2 ∧ p3))) ∨ (((p2 ∨ False) → (p1 ∧ True)) ∧ ((p7 → p4) ∨ (p4 ∧ False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p1 p7 p0 p3 p2 p6 : Prop)
theorem file41_106149 : ((((((True → True) → False) ∧ ((p7 → p1) → False)) ∧ (((p6 ∨ p2) → (p0 → False)) → False)) ∧ ((((p1 → False) ∧ (p1 ∧ p7)) ∧ ((p0 ∧ p3) ∨ (p7 → p1))) ∨ (((True ∧ False) → (p3 → False)) → False))) → False) := by
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    cases assump_32
    case intro assump_34 assump_35 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        cases assump_33
        case inl assump_44 =>
          cases assump_44
          case intro assump_46 assump_47 =>
            cases assump_46
            case intro assump_48 assump_49 =>
              cases assump_49
              case intro assump_52 assump_53 =>
                cases assump_47
                case inl assump_58 =>
                  cases assump_58
                  case intro assump_60 assump_61 =>
                    have assump_100 : p1 := by
                      exact assump_52
                    let assump_70 := assump_48 assump_100
                    apply False.elim assump_70
                case inr assump_59 =>
                  have assump_101 : p1 := by
                    exact assump_52
                  let assump_80 := assump_48 assump_101
                  apply False.elim assump_80
        case inr assump_45 =>
          have assump_102 : ((True ∧ False) → (p3 → False)) := by
            intro assump_87
            intro assump_88
            cases assump_87
            case intro assump_91 assump_92 =>
              apply False.elim assump_92
          let assump_86 := assump_45 assump_102
          apply False.elim assump_86


variable (p0 p4 p7 p6 p5 p1 p2 : Prop)
theorem file41_107808 : (((((p2 ∧ p0) → False) → False) ∧ (((p1 ∧ p2) ∧ (p2 ∨ p6)) ∧ ((p5 → False) ∧ (p5 ∨ p5)))) → ((((p4 → False) → False) ∨ ((p4 → p7) → False)) ∧ (((p6 ∨ p7) ∨ (p6 ∨ p4)) → ((p2 → p7) ∧ (p7 ∧ True))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case inl assump_16 =>
            cases assump_7
            case intro assump_20 assump_21 =>
              cases assump_21
              case inl assump_24 =>
                apply Or.inl
                intro assump_28
                have assump_550 : p5 := by
                  exact assump_24
                let assump_33 := assump_20 assump_550
                apply False.elim assump_33
              case inr assump_25 =>
                apply Or.inl
                intro assump_39
                have assump_551 : p5 := by
                  exact assump_25
                let assump_44 := assump_20 assump_551
                apply False.elim assump_44
          case inr assump_17 =>
            cases assump_7
            case intro assump_50 assump_51 =>
              cases assump_51
              case inl assump_54 =>
                apply Or.inl
                intro assump_58
                have assump_552 : p5 := by
                  exact assump_54
                let assump_63 := assump_50 assump_552
                apply False.elim assump_63
              case inr assump_55 =>
                apply Or.inl
                intro assump_69
                have assump_553 : p5 := by
                  exact assump_55
                let assump_74 := assump_50 assump_553
                apply False.elim assump_74
  intro assump_78
  apply And.intro
  intro assump_79
  cases assump_78
  case inl assump_82 =>
    cases assump_82
    case inl assump_84 =>
      cases assump_1
      case intro assump_88 assump_89 =>
        cases assump_89
        case intro assump_92 assump_93 =>
          cases assump_92
          case intro assump_94 assump_95 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              cases assump_95
              case inl assump_102 =>
                cases assump_93
                case intro assump_106 assump_107 =>
                  cases assump_107
                  case inl assump_110 =>
                    have assump_554 : p5 := by
                      exact assump_110
                    let assump_115 := assump_106 assump_554
                    apply False.elim assump_115
                  case inr assump_111 =>
                    have assump_555 : p5 := by
                      exact assump_111
                    let assump_122 := assump_106 assump_555
                    apply False.elim assump_122
              case inr assump_103 =>
                cases assump_93
                case intro assump_128 assump_129 =>
                  cases assump_129
                  case inl assump_132 =>
                    have assump_556 : p5 := by
                      exact assump_132
                    let assump_137 := assump_128 assump_556
                    apply False.elim assump_137
                  case inr assump_133 =>
                    have assump_557 : p5 := by
                      exact assump_133
                    let assump_144 := assump_128 assump_557
                    apply False.elim assump_144
    case inr assump_85 =>
      cases assump_1
      case intro assump_150 assump_151 =>
        cases assump_151
        case intro assump_154 assump_155 =>
          cases assump_154
          case intro assump_156 assump_157 =>
            cases assump_156
            case intro assump_158 assump_159 =>
              cases assump_157
              case inl assump_164 =>
                cases assump_155
                case intro assump_168 assump_169 =>
                  cases assump_169
                  case inl assump_172 =>
                    exact assump_85
                  case inr assump_173 =>
                    exact assump_85
              case inr assump_165 =>
                cases assump_155
                case intro assump_180 assump_181 =>
                  cases assump_181
                  case inl assump_184 =>
                    exact assump_85
                  case inr assump_185 =>
                    exact assump_85
  case inr assump_83 =>
    cases assump_83
    case inl assump_190 =>
      cases assump_1
      case intro assump_194 assump_195 =>
        cases assump_195
        case intro assump_198 assump_199 =>
          cases assump_198
          case intro assump_200 assump_201 =>
            cases assump_200
            case intro assump_202 assump_203 =>
              cases assump_201
              case inl assump_208 =>
                cases assump_199
                case intro assump_212 assump_213 =>
                  cases assump_213
                  case inl assump_216 =>
                    have assump_558 : p5 := by
                      exact assump_216
                    let assump_221 := assump_212 assump_558
                    apply False.elim assump_221
                  case inr assump_217 =>
                    have assump_559 : p5 := by
                      exact assump_217
                    let assump_228 := assump_212 assump_559
                    apply False.elim assump_228
              case inr assump_209 =>
                cases assump_199
                case intro assump_234 assump_235 =>
                  cases assump_235
                  case inl assump_238 =>
                    have assump_560 : p5 := by
                      exact assump_238
                    let assump_243 := assump_234 assump_560
                    apply False.elim assump_243
                  case inr assump_239 =>
                    have assump_561 : p5 := by
                      exact assump_239
                    let assump_250 := assump_234 assump_561
                    apply False.elim assump_250
    case inr assump_191 =>
      cases assump_1
      case intro assump_256 assump_257 =>
        cases assump_257
        case intro assump_260 assump_261 =>
          cases assump_260
          case intro assump_262 assump_263 =>
            cases assump_262
            case intro assump_264 assump_265 =>
              cases assump_263
              case inl assump_270 =>
                cases assump_261
                case intro assump_274 assump_275 =>
                  cases assump_275
                  case inl assump_278 =>
                    have assump_562 : p5 := by
                      exact assump_278
                    let assump_283 := assump_274 assump_562
                    apply False.elim assump_283
                  case inr assump_279 =>
                    have assump_563 : p5 := by
                      exact assump_279
                    let assump_290 := assump_274 assump_563
                    apply False.elim assump_290
              case inr assump_271 =>
                cases assump_261
                case intro assump_296 assump_297 =>
                  cases assump_297
                  case inl assump_300 =>
                    have assump_564 : p5 := by
                      exact assump_300
                    let assump_305 := assump_296 assump_564
                    apply False.elim assump_305
                  case inr assump_301 =>
                    have assump_565 : p5 := by
                      exact assump_301
                    let assump_312 := assump_296 assump_565
                    apply False.elim assump_312
  apply And.intro
  cases assump_78
  case inl assump_316 =>
    cases assump_316
    case inl assump_318 =>
      cases assump_1
      case intro assump_322 assump_323 =>
        cases assump_323
        case intro assump_326 assump_327 =>
          cases assump_326
          case intro assump_328 assump_329 =>
            cases assump_328
            case intro assump_330 assump_331 =>
              cases assump_329
              case inl assump_336 =>
                cases assump_327
                case intro assump_340 assump_341 =>
                  cases assump_341
                  case inl assump_344 =>
                    have assump_566 : p5 := by
                      exact assump_344
                    let assump_349 := assump_340 assump_566
                    apply False.elim assump_349
                  case inr assump_345 =>
                    have assump_567 : p5 := by
                      exact assump_345
                    let assump_356 := assump_340 assump_567
                    apply False.elim assump_356
              case inr assump_337 =>
                cases assump_327
                case intro assump_362 assump_363 =>
                  cases assump_363
                  case inl assump_366 =>
                    have assump_568 : p5 := by
                      exact assump_366
                    let assump_371 := assump_362 assump_568
                    apply False.elim assump_371
                  case inr assump_367 =>
                    have assump_569 : p5 := by
                      exact assump_367
                    let assump_378 := assump_362 assump_569
                    apply False.elim assump_378
    case inr assump_319 =>
      cases assump_1
      case intro assump_384 assump_385 =>
        cases assump_385
        case intro assump_388 assump_389 =>
          cases assump_388
          case intro assump_390 assump_391 =>
            cases assump_390
            case intro assump_392 assump_393 =>
              cases assump_391
              case inl assump_398 =>
                cases assump_389
                case intro assump_402 assump_403 =>
                  cases assump_403
                  case inl assump_406 =>
                    exact assump_319
                  case inr assump_407 =>
                    exact assump_319
              case inr assump_399 =>
                cases assump_389
                case intro assump_414 assump_415 =>
                  cases assump_415
                  case inl assump_418 =>
                    exact assump_319
                  case inr assump_419 =>
                    exact assump_319
  case inr assump_317 =>
    cases assump_317
    case inl assump_424 =>
      cases assump_1
      case intro assump_428 assump_429 =>
        cases assump_429
        case intro assump_432 assump_433 =>
          cases assump_432
          case intro assump_434 assump_435 =>
            cases assump_434
            case intro assump_436 assump_437 =>
              cases assump_435
              case inl assump_442 =>
                cases assump_433
                case intro assump_446 assump_447 =>
                  cases assump_447
                  case inl assump_450 =>
                    have assump_570 : p5 := by
                      exact assump_450
                    let assump_455 := assump_446 assump_570
                    apply False.elim assump_455
                  case inr assump_451 =>
                    have assump_571 : p5 := by
                      exact assump_451
                    let assump_462 := assump_446 assump_571
                    apply False.elim assump_462
              case inr assump_443 =>
                cases assump_433
                case intro assump_468 assump_469 =>
                  cases assump_469
                  case inl assump_472 =>
                    have assump_572 : p5 := by
                      exact assump_472
                    let assump_477 := assump_468 assump_572
                    apply False.elim assump_477
                  case inr assump_473 =>
                    have assump_573 : p5 := by
                      exact assump_473
                    let assump_484 := assump_468 assump_573
                    apply False.elim assump_484
    case inr assump_425 =>
      cases assump_1
      case intro assump_490 assump_491 =>
        cases assump_491
        case intro assump_494 assump_495 =>
          cases assump_494
          case intro assump_496 assump_497 =>
            cases assump_496
            case intro assump_498 assump_499 =>
              cases assump_497
              case inl assump_504 =>
                cases assump_495
                case intro assump_508 assump_509 =>
                  cases assump_509
                  case inl assump_512 =>
                    have assump_574 : p5 := by
                      exact assump_512
                    let assump_517 := assump_508 assump_574
                    apply False.elim assump_517
                  case inr assump_513 =>
                    have assump_575 : p5 := by
                      exact assump_513
                    let assump_524 := assump_508 assump_575
                    apply False.elim assump_524
              case inr assump_505 =>
                cases assump_495
                case intro assump_530 assump_531 =>
                  cases assump_531
                  case inl assump_534 =>
                    have assump_576 : p5 := by
                      exact assump_534
                    let assump_539 := assump_530 assump_576
                    apply False.elim assump_539
                  case inr assump_535 =>
                    have assump_577 : p5 := by
                      exact assump_535
                    let assump_546 := assump_530 assump_577
                    apply False.elim assump_546
  apply True.intro


variable (p2 p1 p0 p4 p7 : Prop)
theorem file41_121496 : (((((p0 ∧ True) → (p4 → p0)) ∧ ((False ∧ p2) → False)) → (((p0 ∨ True) → False) ∨ ((True ∨ p2) → False))) → ((((p7 → True) ∨ (p1 → p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_38 : (((p0 ∧ True) → (p4 → p0)) ∧ ((False ∧ p2) → False)) := by
    apply And.intro
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      exact assump_12
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      apply False.elim assump_19
  let assump_7 := assump_1 assump_38
  cases assump_7
  case inl assump_24 =>
    have assump_39 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_28 := assump_24 assump_39
    apply False.elim assump_28
  case inr assump_25 =>
    have assump_40 : (True ∨ p2) := by
      apply Or.inl
      apply True.intro
    let assump_34 := assump_25 assump_40
    apply False.elim assump_34


variable (p7 p2 p6 p1 p3 p4 p5 p0 : Prop)
theorem file41_122491 : (((((p7 ∧ p4) ∧ (p4 → False)) ∧ ((p1 ∧ p2) → (p3 ∨ p4))) ∧ (((False → p2) → (p1 → p0)) ∨ ((True → p3) ∧ (p5 → p2)))) → ((((p5 → False) → (p3 ∧ p5)) ∧ ((p0 → p6) ∧ (p3 → True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_14
              case inl assump_29 =>
                have assump_57 : p4 := by
                  exact assump_20
                let assump_39 := assump_18 assump_57
                apply False.elim assump_39
              case inr assump_30 =>
                cases assump_30
                case intro assump_43 assump_44 =>
                  have assump_58 : p4 := by
                    exact assump_20
                  let assump_53 := assump_18 assump_58
                  apply False.elim assump_53


variable (p2 p1 p5 p3 p7 p6 p0 : Prop)
theorem file41_123694 : (((((p5 ∨ False) → False) → False) ∧ (((False → False) → (p3 ∨ p5)) ∨ ((p0 → p7) → False))) → ((((p7 ∧ p6) ∧ (p2 ∨ p0)) → ((False ∧ p1) → (p3 ∧ p1))) ∨ (((p6 ∨ p7) → (True → False)) → ((False → False) → (p6 ∧ p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      apply And.intro
      cases assump_11
      case intro assump_12 assump_13 =>
        apply False.elim assump_12
      cases assump_11
      case intro assump_16 assump_17 =>
        apply False.elim assump_16
    case inr assump_7 =>
      apply Or.inl
      intro assump_22
      intro assump_23
      apply And.intro
      cases assump_23
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
      cases assump_23
      case intro assump_28 assump_29 =>
        apply False.elim assump_28


variable (p3 p4 p1 p7 p2 p0 p5 p6 : Prop)
theorem file41_124678 : (((((p2 → False) → (p4 ∧ p0)) → False) ∧ (((p5 → False) ∧ (p3 ∧ p3)) ∧ ((p6 → p5) → False))) → ((((p7 ∨ p2) → (False → p4)) → ((p6 → p3) ∨ (False ∨ p5))) ∨ (((p4 ∨ p7) ∧ (p6 ∨ p1)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_20
          apply Or.inl
          intro assump_23
          exact assump_13


