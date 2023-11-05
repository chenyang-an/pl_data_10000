variable (p0 p7 p2 p6 p4 p1 p3 : Prop)
theorem file43_47 : (((((False ∧ p3) → False) → False) → False) ∨ ((((p7 ∨ True) → (p4 ∧ p0)) ∧ ((p6 ∨ p1) ∨ (p7 ∧ p6))) ∧ (((False → p2) ∨ (p1 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((False ∧ p3) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p6 p4 p0 : Prop)
theorem file43_503 : (((((p6 ∧ p6) → False) → ((p3 → p0) ∧ (p0 → False))) ∧ (((True → False) → (p0 → p4)) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_28 : ((True → False) → (p0 → p4)) := by
      intro assump_15
      intro assump_16
      have assump_29 : True := by
        apply True.intro
      let assump_21 := assump_15 assump_29
      apply False.elim assump_21
    let assump_14 := assump_9 assump_28
    apply False.elim assump_14


variable (p0 p6 p4 p3 p7 p2 : Prop)
theorem file43_1047 : ((((((p0 ∧ p0) ∧ (p0 → False)) → False) → (((p0 ∧ p4) → (True ∨ p2)) ∨ ((p7 ∨ p4) ∨ (p6 → p3)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 ∧ p0) ∧ (p0 → False)) → False) → (((p0 ∧ p4) → (True ∨ p2)) ∨ ((p7 ∨ p4) ∨ (p6 → p3)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p1 p3 p7 p2 p6 p5 : Prop)
theorem file43_1586 : (((((p7 → False) → False) ∧ ((p0 ∧ p2) ∧ (False ∧ p0))) → (((True → p1) → (p1 → p3)) → False)) ∨ ((((p5 ∨ True) ∧ (True ∧ p7)) ∨ ((p6 ∨ p2) → False)) → (((p1 → True) → (p1 ∨ p6)) ∨ ((p5 ∨ p2) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          apply False.elim assump_17


variable (p2 p0 p7 p6 p3 : Prop)
theorem file43_2173 : ((((((False → False) ∧ (p6 → False)) ∧ ((False → True) → False)) → (((p0 → p7) ∨ (p2 → p3)) ∨ ((p6 → p6) → False))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((False → False) ∧ (p6 → False)) ∧ ((False → True) → False)) → (((p0 → p7) ∨ (p2 → p3)) ∨ ((p6 → p6) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_16
        have assump_29 : (False → True) := by
          intro assump_21
          apply True.intro
        let assump_20 := assump_7 assump_29
        apply False.elim assump_20
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p6 p1 p3 p7 p2 p4 p5 : Prop)
theorem file43_2974 : ((((((p2 ∨ p3) ∧ (False ∧ p5)) → ((p2 → p6) → False)) → False) ∧ ((((False → p7) → False) → ((p4 ∧ p1) ∨ (p3 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → p7) → False) → ((p4 ∧ p1) ∨ (p3 ∧ p2))) := by
      intro assump_9
      have assump_23 : (False → p7) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p5 p6 p3 p2 p7 p1 p4 p0 : Prop)
theorem file43_3594 : ((((((p3 ∨ p2) ∨ (p0 ∧ p2)) → ((p3 ∨ p1) ∨ (p1 → False))) → (((p1 → p0) ∨ (p7 ∧ p5)) → ((True ∨ p5) ∨ (p0 → False)))) → ((((p4 → False) → (p2 ∨ True)) → False) ∧ (((False → p2) ∧ (p3 ∨ p3)) ∨ ((p6 → p5) ∧ (p1 → False))))) → False) := by
  intro assump_1
  have assump_29 : ((((p3 ∨ p2) ∨ (p0 ∧ p2)) → ((p3 ∨ p1) ∨ (p1 → False))) → (((p1 → p0) ∨ (p7 ∧ p5)) → ((True ∨ p5) ∨ (p0 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_13 assump_14 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
  let assump_4 := assump_1 assump_29
  let assump_21 := And.left assump_4
  have assump_30 : ((p4 → False) → (p2 ∨ True)) := by
    intro assump_23
    apply Or.inr
    apply True.intro
  let assump_22 := assump_21 assump_30
  apply False.elim assump_22


variable (p4 p3 : Prop)
theorem file43_4587 : (((((p3 → p4) → False) → ((p4 → False) ∨ (p3 → False))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p3 → p4) → False) → ((p4 → False) ∨ (p3 → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_23 : (p3 → p4) := by
      intro assump_13
      exact assump_8
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p5 p7 p3 p6 p2 p1 : Prop)
theorem file43_5097 : ((((((p5 → p3) → (p5 → p5)) → False) ∧ (((p2 ∧ True) ∨ (p6 ∨ p2)) → ((p7 → p1) → (p0 ∧ False)))) ∧ ((((p3 ∨ p5) ∧ (False → False)) → False) ∨ (((p3 ∧ p5) ∧ (p1 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        have assump_40 : ((p5 → p3) → (p5 → p5)) := by
          intro assump_17
          intro assump_18
          exact assump_18
        let assump_16 := assump_4 assump_40
        apply False.elim assump_16
      case inr assump_11 =>
        have assump_41 : ((p5 → p3) → (p5 → p5)) := by
          intro assump_31
          intro assump_32
          exact assump_32
        let assump_30 := assump_4 assump_41
        apply False.elim assump_30


variable (p0 p5 p7 p1 p6 : Prop)
theorem file43_5974 : ((((((True → False) → (p5 → False)) ∨ ((p7 ∨ p0) → (p5 → p6))) ∨ (((p1 ∧ p1) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True → False) → (p5 → False)) ∨ ((p7 ∨ p0) → (p5 → p6))) ∨ (((p1 ∧ p1) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p5 p3 p1 p7 : Prop)
theorem file43_6550 : ((((((True → False) → (p3 ∨ p1)) ∧ ((p5 → False) ∨ (True ∨ p7))) → (((p1 ∧ p5) → False) → ((True → True) ∧ (p4 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((True → False) → (p3 ∨ p1)) ∧ ((p5 → False) ∨ (True ∨ p7))) → (((p1 ∧ p5) → False) → ((True → True) ∧ (p4 → True)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    apply True.intro
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p1 p0 : Prop)
theorem file43_7109 : ((((((p0 ∨ True) → False) ∧ ((p1 ∧ p1) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p0 ∨ True) → False) ∧ ((p1 ∧ p1) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p7 p3 p5 p4 : Prop)
theorem file43_7644 : ((((((p7 → p5) → (p4 ∧ p3)) → ((p3 ∧ p5) ∨ (False ∨ True))) ∧ (((p7 ∨ True) ∧ (True ∧ True)) ∧ ((p4 ∨ True) → (True ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p7 → p5) → (p4 ∧ p3)) → ((p3 ∧ p5) ∨ (False ∨ True))) ∧ (((p7 ∨ True) ∧ (True ∧ True)) ∧ ((p4 ∨ True) → (True ∨ True)))) := by
    apply And.intro
    intro assump_5
    apply Or.inr
    apply Or.inr
    apply True.intro
    apply And.intro
    apply And.intro
    apply Or.inr
    apply True.intro
    apply And.intro
    apply True.intro
    apply True.intro
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      apply Or.inl
      apply True.intro
    case inr assump_10 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p7 p1 p4 p2 p3 p0 p6 : Prop)
theorem file43_8500 : (((((p6 → p2) ∨ (p7 ∧ p4)) ∧ ((p3 ∨ p2) → False)) ∨ (((p1 ∧ p5) ∧ (p0 → p3)) → False)) → ((((p4 ∨ p5) ∧ (p1 ∨ False)) ∧ ((p5 → False) ∨ (p0 → True))) ∨ (((p4 ∧ False) ∧ (p3 ∨ p5)) → ((p2 ∧ p5) ∧ (False ∨ p1))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inr
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
        cases assump_12
        case intro assump_29 assump_30 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            apply False.elim assump_32
      case inr assump_7 =>
        cases assump_7
        case intro assump_37 assump_38 =>
          apply Or.inr
          intro assump_45
          apply And.intro
          apply And.intro
          cases assump_45
          case intro assump_46 assump_47 =>
            cases assump_46
            case intro assump_48 assump_49 =>
              apply False.elim assump_49
          cases assump_45
          case intro assump_54 assump_55 =>
            cases assump_54
            case intro assump_56 assump_57 =>
              apply False.elim assump_57
          cases assump_45
          case intro assump_62 assump_63 =>
            cases assump_62
            case intro assump_64 assump_65 =>
              apply False.elim assump_65
  case inr assump_3 =>
    apply Or.inr
    intro assump_72
    apply And.intro
    apply And.intro
    cases assump_72
    case intro assump_73 assump_74 =>
      cases assump_73
      case intro assump_75 assump_76 =>
        apply False.elim assump_76
    cases assump_72
    case intro assump_81 assump_82 =>
      cases assump_81
      case intro assump_83 assump_84 =>
        apply False.elim assump_84
    cases assump_72
    case intro assump_89 assump_90 =>
      cases assump_89
      case intro assump_91 assump_92 =>
        apply False.elim assump_92


variable (p4 p6 p7 p2 p0 p1 : Prop)
theorem file43_10869 : (((((p2 ∧ False) → False) → False) → False) ∨ ((((p6 → p0) → (p6 ∧ p1)) → ((p1 ∧ p2) → False)) ∧ (((p0 ∨ p7) ∨ (p4 ∧ p1)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p2 ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p2 p1 p6 p0 p5 p4 p3 : Prop)
theorem file43_11325 : (((((p7 ∨ False) → (p1 ∨ p4)) ∨ ((p4 ∨ p3) ∨ (p3 ∧ p1))) ∧ (((p6 → p6) ∧ (p0 → False)) ∧ ((p5 → p0) ∧ (False → False)))) → ((((p4 → False) ∧ (p3 → False)) ∧ ((True ∨ p2) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_14
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_20
              case intro assump_27 assump_28 =>
                have assump_126 : (True ∨ p2) := by
                  apply Or.inl
                  apply True.intro
                let assump_38 := assump_4 assump_126
                apply False.elim assump_38
        case inr assump_16 =>
          cases assump_16
          case inl assump_42 =>
            cases assump_42
            case inl assump_44 =>
              cases assump_14
              case intro assump_48 assump_49 =>
                cases assump_48
                case intro assump_50 assump_51 =>
                  cases assump_49
                  case intro assump_56 assump_57 =>
                    have assump_127 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_67 := assump_4 assump_127
                    apply False.elim assump_67
            case inr assump_45 =>
              cases assump_14
              case intro assump_73 assump_74 =>
                cases assump_73
                case intro assump_75 assump_76 =>
                  cases assump_74
                  case intro assump_81 assump_82 =>
                    have assump_128 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_92 := assump_4 assump_128
                    apply False.elim assump_92
          case inr assump_43 =>
            cases assump_43
            case intro assump_96 assump_97 =>
              cases assump_14
              case intro assump_102 assump_103 =>
                cases assump_102
                case intro assump_104 assump_105 =>
                  cases assump_103
                  case intro assump_110 assump_111 =>
                    have assump_129 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_122 := assump_4 assump_129
                    apply False.elim assump_122


variable (p7 p3 p6 p0 p4 p2 p5 : Prop)
theorem file43_14015 : (((((p2 ∨ p5) ∧ (p5 → False)) → ((p7 → False) ∧ (False ∧ p2))) → False) → ((((p7 ∨ p0) → False) → ((p5 ∨ p0) → False)) ∨ (((p2 → p6) ∨ (True ∨ p3)) ∨ ((p2 ∧ p7) ∨ (p4 ∨ p7))))) := by
  intro assump_5
  apply Or.inl
  intro assump_8
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    have assump_90 : (((p2 ∨ p5) ∧ (p5 → False)) → ((p7 → False) ∧ (False ∧ p2))) := by
      intro assump_19
      apply And.intro
      intro assump_20
      cases assump_19
      case intro assump_23 assump_24 =>
        cases assump_23
        case inl assump_25 =>
          have assump_91 : p5 := by
            exact assump_10
          let assump_31 := assump_24 assump_91
          apply False.elim assump_31
        case inr assump_26 =>
          have assump_92 : p5 := by
            exact assump_26
          let assump_39 := assump_24 assump_92
          apply False.elim assump_39
      apply And.intro
      cases assump_19
      case intro assump_43 assump_44 =>
        cases assump_43
        case inl assump_45 =>
          have assump_93 : p5 := by
            exact assump_10
          let assump_51 := assump_44 assump_93
          apply False.elim assump_51
        case inr assump_46 =>
          have assump_94 : p5 := by
            exact assump_46
          let assump_59 := assump_44 assump_94
          apply False.elim assump_59
      cases assump_19
      case intro assump_63 assump_64 =>
        cases assump_63
        case inl assump_65 =>
          exact assump_65
        case inr assump_66 =>
          have assump_95 : p5 := by
            exact assump_66
          let assump_75 := assump_64 assump_95
          apply False.elim assump_75
    let assump_18 := assump_5 assump_90
    apply False.elim assump_18
  case inr assump_11 =>
    have assump_96 : (p7 ∨ p0) := by
      apply Or.inr
      exact assump_11
    let assump_86 := assump_8 assump_96
    apply False.elim assump_86


variable (p1 p0 p5 : Prop)
theorem file43_15980 : (((((True → False) ∧ (p1 ∧ p0)) → ((p5 ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((True → False) ∧ (p1 ∧ p0)) → ((p5 ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p4 : Prop)
theorem file43_16395 : (((((False ∨ False) ∧ (p4 ∧ False)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((False ∨ False) ∧ (p4 ∧ False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p6 p2 p4 p1 p7 : Prop)
theorem file43_16891 : (((((p7 ∨ True) ∨ (p4 ∨ True)) → False) → False) ∨ ((((p5 → False) → (p2 ∨ p4)) → False) → (((p6 → False) → False) ∧ ((True → False) ∧ (p1 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((p7 ∨ True) ∨ (p4 ∨ True)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p4 p1 : Prop)
theorem file43_17302 : (((((False ∨ True) ∨ (p1 ∨ False)) ∨ ((p2 → False) → (p1 → p4))) → False) → False) := by
  intro assump_1
  have assump_8 : (((False ∨ True) ∨ (p1 ∨ False)) ∨ ((p2 → False) → (p1 → p4))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p0 p5 p6 p1 p4 p2 : Prop)
theorem file43_17691 : (((((False ∧ False) ∨ (p2 → False)) → ((p5 ∧ p2) ∨ (p6 → p6))) → False) → ((((p1 → False) → False) → ((p0 ∨ True) → (p1 ∧ p4))) → False)) := by
  intro assump_5
  intro assump_6
  have assump_27 : (((False ∧ False) ∨ (p2 → False)) → ((p5 ∧ p2) ∨ (p6 → p6))) := by
    intro assump_12
    cases assump_12
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
    case inr assump_14 =>
      apply Or.inr
      intro assump_21
      exact assump_21
  let assump_11 := assump_5 assump_27
  apply False.elim assump_11


variable (p7 p6 p1 p0 : Prop)
theorem file43_18328 : ((((((p0 → False) → False) → ((p6 ∨ True) ∧ (p6 → False))) ∧ (((True → False) → False) → False)) ∧ ((((p7 ∧ False) ∨ (False ∧ p1)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_29 : (((p7 ∧ False) ∨ (False ∧ p1)) → False) := by
        intro assump_13
        cases assump_13
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
        case inr assump_15 =>
          cases assump_15
          case intro assump_22 assump_23 =>
            apply False.elim assump_22
      let assump_12 := assump_3 assump_29
      apply False.elim assump_12


variable (p4 p0 p5 p6 p1 p7 p2 p3 : Prop)
theorem file43_19152 : (((((True ∨ p4) ∧ (p6 → p5)) → ((p7 ∨ p3) ∨ (False → p5))) ∨ (((p0 → p1) ∨ (p1 ∨ p3)) ∨ ((p2 ∧ False) ∨ (p5 ∨ p0)))) → ((((p0 ∨ p1) → False) → ((p0 → p3) ∨ (p0 ∧ p5))) ∨ (((p2 → False) → False) → ((p5 ∧ p0) ∧ (p6 ∧ p3))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply Or.inl
    intro assump_9
    have assump_93 : (p0 ∨ p1) := by
      apply Or.inl
      exact assump_9
    let assump_13 := assump_6 assump_93
    apply False.elim assump_13
  case inr assump_3 =>
    cases assump_3
    case inl assump_17 =>
      cases assump_17
      case inl assump_19 =>
        apply Or.inl
        intro assump_23
        apply Or.inl
        intro assump_26
        have assump_94 : (p0 ∨ p1) := by
          apply Or.inl
          exact assump_26
        let assump_30 := assump_23 assump_94
        apply False.elim assump_30
      case inr assump_20 =>
        cases assump_20
        case inl assump_34 =>
          apply Or.inl
          intro assump_38
          apply Or.inl
          intro assump_41
          have assump_95 : (p0 ∨ p1) := by
            apply Or.inl
            exact assump_41
          let assump_45 := assump_38 assump_95
          apply False.elim assump_45
        case inr assump_35 =>
          apply Or.inl
          intro assump_51
          apply Or.inl
          intro assump_54
          exact assump_35
    case inr assump_18 =>
      cases assump_18
      case inl assump_57 =>
        cases assump_57
        case intro assump_59 assump_60 =>
          apply False.elim assump_60
      case inr assump_58 =>
        cases assump_58
        case inl assump_65 =>
          apply Or.inl
          intro assump_69
          apply Or.inl
          intro assump_72
          have assump_96 : (p0 ∨ p1) := by
            apply Or.inl
            exact assump_72
          let assump_76 := assump_69 assump_96
          apply False.elim assump_76
        case inr assump_66 =>
          apply Or.inl
          intro assump_82
          apply Or.inl
          intro assump_85
          have assump_97 : (p0 ∨ p1) := by
            apply Or.inl
            exact assump_85
          let assump_89 := assump_82 assump_97
          apply False.elim assump_89


variable (p3 p6 p5 p4 p7 p0 p1 : Prop)
theorem file43_21460 : ((((((p3 ∧ p4) → False) ∨ ((p7 ∨ p1) → False)) ∧ (((True → p7) ∨ (False ∧ p1)) ∧ ((p3 ∨ p6) → (p0 ∨ p5)))) ∧ ((((p6 ∨ p5) ∨ (p1 ∧ p3)) ∨ ((p4 → False) → (False → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            have assump_56 : (((p6 ∨ p5) ∨ (p1 ∧ p3)) ∨ ((p4 → False) → (False → p7))) := by
              apply Or.inr
              intro assump_21
              intro assump_22
              apply False.elim assump_22
            let assump_20 := assump_3 assump_56
            apply False.elim assump_20
          case inr assump_13 =>
            cases assump_13
            case intro assump_28 assump_29 =>
              apply False.elim assump_28
      case inr assump_7 =>
        cases assump_5
        case intro assump_34 assump_35 =>
          cases assump_34
          case inl assump_36 =>
            have assump_57 : (((p6 ∨ p5) ∨ (p1 ∧ p3)) ∨ ((p4 → False) → (False → p7))) := by
              apply Or.inr
              intro assump_45
              intro assump_46
              apply False.elim assump_46
            let assump_44 := assump_3 assump_57
            apply False.elim assump_44
          case inr assump_37 =>
            cases assump_37
            case intro assump_52 assump_53 =>
              apply False.elim assump_52


variable (p4 p6 p3 p5 p1 : Prop)
theorem file43_23064 : ((((((False → p5) → (p5 ∧ False)) ∨ ((p6 → False) ∧ (p6 ∧ p3))) → (((p4 ∧ p4) → False) ∨ ((True ∧ p5) ∧ (p1 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_56 : ((((False → p5) → (p5 ∧ False)) ∨ ((p6 → False) ∧ (p6 ∧ p3))) → (((p4 ∧ p4) → False) ∨ ((True ∧ p5) ∧ (p1 ∨ p3)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        have assump_57 : (False → p5) := by
          intro assump_20
          apply False.elim assump_20
        let assump_19 := assump_6 assump_57
        let assump_23 := And.right assump_19
        apply False.elim assump_23
    case inr assump_7 =>
      cases assump_7
      case intro assump_28 assump_29 =>
        cases assump_29
        case intro assump_32 assump_33 =>
          apply Or.inl
          intro assump_38
          cases assump_38
          case intro assump_39 assump_40 =>
            have assump_58 : p6 := by
              exact assump_32
            let assump_49 := assump_28 assump_58
            apply False.elim assump_49
  let assump_4 := assump_1 assump_56
  apply False.elim assump_4


variable (p0 p2 p4 p6 : Prop)
theorem file43_24305 : ((((((p6 ∨ p2) ∨ (False → False)) → False) → (((p4 → True) → (False ∨ False)) ∧ ((p0 → p2) → False))) → False) → False) := by
  intro assump_5
  have assump_37 : ((((p6 ∨ p2) ∨ (False → False)) → False) → (((p4 → True) → (False ∨ False)) ∧ ((p0 → p2) → False))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    have assump_38 : ((p6 ∨ p2) ∨ (False → False)) := by
      apply Or.inr
      intro assump_16
      apply False.elim assump_16
    let assump_15 := assump_9 assump_38
    apply False.elim assump_15
    intro assump_22
    have assump_39 : ((p6 ∨ p2) ∨ (False → False)) := by
      apply Or.inr
      intro assump_28
      apply False.elim assump_28
    let assump_27 := assump_9 assump_39
    apply False.elim assump_27
  let assump_8 := assump_5 assump_37
  apply False.elim assump_8


variable (p3 p1 p2 p4 p5 p7 p0 p6 : Prop)
theorem file43_25187 : (((((p5 ∨ p0) → False) → ((p7 → False) → (p5 → False))) ∨ (((False → p4) → (p2 ∧ p1)) → False)) ∨ ((((p1 ∨ True) → (p1 ∨ p5)) ∨ ((False ∨ p2) ∧ (p6 ∨ p3))) → (((False ∨ p4) → (p7 ∧ p7)) ∨ ((p5 ∨ p1) ∨ (p6 → p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_14 : (p5 ∨ p0) := by
    apply Or.inl
    exact assump_3
  let assump_10 := assump_1 assump_14
  apply False.elim assump_10


variable (p4 p6 p7 p0 p2 : Prop)
theorem file43_25684 : (((((p0 → False) ∨ (p7 ∨ False)) → ((p2 → True) ∨ (p4 ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_21 : (((p0 → False) ∨ (p7 ∨ False)) → ((p2 → True) ∨ (p4 ∨ p6))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case inl assump_11 =>
        apply Or.inl
        intro assump_15
        apply True.intro
      case inr assump_12 =>
        apply False.elim assump_12
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p0 p1 p3 p2 p7 p6 p5 p4 : Prop)
theorem file43_26337 : (((((p0 ∨ True) ∧ (True ∨ p5)) ∧ ((p2 ∨ p7) ∧ (True → True))) ∨ (((p7 ∨ True) → (p2 ∧ p5)) → ((p3 → p3) ∨ (p7 ∧ True)))) ∨ ((((p1 ∨ p0) → False) → ((p0 ∧ p0) ∧ (p5 → p1))) ∨ (((p1 ∧ p6) → (p4 ∨ True)) → ((p0 ∨ p6) → False)))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply Or.inl
  intro assump_4
  exact assump_4


variable (p2 p3 p4 p7 p6 p1 p5 : Prop)
theorem file43_26728 : (((((False ∨ True) → False) → ((p4 → p4) → False)) ∨ (((p1 ∧ p7) → False) → ((p2 → p3) ∨ (p5 → False)))) ∨ ((((False → False) → (p6 → p5)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : (False ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p6 p0 p2 p7 p3 : Prop)
theorem file43_27156 : ((((((p3 ∧ p0) → False) → ((p6 → p2) → False)) → (((p6 ∨ p7) → (False → False)) → False)) ∧ ((((p3 ∨ True) → False) ∧ ((p2 ∨ p7) → False)) ∨ (((p6 → False) → (p6 → p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_35 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_15 := assump_8 assump_35
        apply False.elim assump_15
    case inr assump_7 =>
      have assump_36 : ((p6 → False) → (p6 → p2)) := by
        intro assump_22
        intro assump_23
        have assump_37 : p6 := by
          exact assump_23
        let assump_28 := assump_22 assump_37
        apply False.elim assump_28
      let assump_21 := assump_7 assump_36
      apply False.elim assump_21


variable (p1 p0 p7 p3 p6 p5 : Prop)
theorem file43_28098 : (((((p3 ∧ False) → (p7 → False)) → False) → (((p0 ∧ p6) → (p0 → p0)) → ((p3 → False) ∧ (p1 ∨ p1)))) ∨ ((((False → False) ∧ (p0 → False)) ∧ ((p6 ∧ p5) → (True ∧ p6))) → False)) := by
  apply Or.inl
  intro assump_12
  intro assump_13
  apply And.intro
  intro assump_14
  have assump_53 : ((p3 ∧ False) → (p7 → False)) := by
    intro assump_22
    intro assump_23
    cases assump_22
    case intro assump_26 assump_27 =>
      apply False.elim assump_27
  let assump_21 := assump_12 assump_53
  apply False.elim assump_21
  have assump_54 : ((p3 ∧ False) → (p7 → False)) := by
    intro assump_40
    intro assump_41
    cases assump_40
    case intro assump_44 assump_45 =>
      apply False.elim assump_45
  let assump_39 := assump_12 assump_54
  apply False.elim assump_39


variable (p6 p0 p4 p2 p5 p1 p7 : Prop)
theorem file43_28938 : (((((p2 ∧ p2) → (p4 ∨ p1)) ∨ ((False ∨ False) → False)) ∨ (((p7 ∧ p2) ∨ (p0 → p0)) → False)) → ((((True ∨ p2) ∨ (p5 → False)) → False) → (((True ∨ p6) ∨ (p2 → p1)) ∧ ((p6 ∨ p5) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  case inr assump_6 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  intro assump_15
  cases assump_15
  case inl assump_16 =>
    cases assump_1
    case inl assump_22 =>
      cases assump_22
      case inl assump_24 =>
        have assump_80 : ((True ∨ p2) ∨ (p5 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_29 := assump_2 assump_80
        apply False.elim assump_29
      case inr assump_25 =>
        have assump_81 : ((True ∨ p2) ∨ (p5 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_36 := assump_2 assump_81
        apply False.elim assump_36
    case inr assump_23 =>
      have assump_82 : ((p7 ∧ p2) ∨ (p0 → p0)) := by
        apply Or.inr
        intro assump_43
        exact assump_43
      let assump_42 := assump_23 assump_82
      apply False.elim assump_42
  case inr assump_17 =>
    cases assump_1
    case inl assump_53 =>
      cases assump_53
      case inl assump_55 =>
        have assump_83 : ((True ∨ p2) ∨ (p5 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_60 := assump_2 assump_83
        apply False.elim assump_60
      case inr assump_56 =>
        have assump_84 : ((True ∨ p2) ∨ (p5 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_67 := assump_2 assump_84
        apply False.elim assump_67
    case inr assump_54 =>
      have assump_85 : ((p7 ∧ p2) ∨ (p0 → p0)) := by
        apply Or.inr
        intro assump_74
        exact assump_74
      let assump_73 := assump_54 assump_85
      apply False.elim assump_73


variable (p0 p4 p6 p7 p3 p1 p5 : Prop)
theorem file43_31183 : ((((((p1 ∨ p4) ∨ (p1 ∨ p1)) ∨ ((p3 ∧ True) ∨ (True ∨ p6))) → False) ∨ ((((p1 ∨ True) → False) ∧ ((p0 ∨ p5) → (p3 ∨ p7))) ∨ (((True ∧ False) → (p1 ∧ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_42 : (((p1 ∨ p4) ∨ (p1 ∨ p1)) ∨ ((p3 ∧ True) ∨ (True ∨ p6))) := by
      apply Or.inr
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_6 := assump_2 assump_42
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_43 : (p1 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_19 := assump_12 assump_43
        apply False.elim assump_19
    case inr assump_11 =>
      have assump_44 : ((True ∧ False) → (p1 ∧ p5)) := by
        intro assump_26
        apply And.intro
        cases assump_26
        case intro assump_27 assump_28 =>
          apply False.elim assump_28
        cases assump_26
        case intro assump_33 assump_34 =>
          apply False.elim assump_34
      let assump_25 := assump_11 assump_44
      apply False.elim assump_25


variable (p4 p3 p0 p6 p7 p1 : Prop)
theorem file43_32428 : (((((p6 ∧ True) → (p4 → p6)) → False) ∧ (((True ∨ True) ∧ (p6 → False)) ∨ ((p6 ∨ p6) ∨ (p7 → False)))) → ((((p4 ∨ p0) ∧ (p3 ∨ p6)) ∨ ((p1 → False) → False)) ∨ (((p3 → False) → (p1 → False)) → ((False ∨ p0) → (p6 ∨ p0))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          apply Or.inr
          intro assump_16
          have assump_125 : ((p6 ∧ True) → (p4 → p6)) := by
            intro assump_22
            intro assump_23
            cases assump_22
            case intro assump_26 assump_27 =>
              exact assump_26
          let assump_21 := assump_2 assump_125
          apply False.elim assump_21
        case inr assump_11 =>
          apply Or.inl
          apply Or.inr
          intro assump_39
          have assump_126 : ((p6 ∧ True) → (p4 → p6)) := by
            intro assump_45
            intro assump_46
            cases assump_45
            case intro assump_49 assump_50 =>
              exact assump_49
          let assump_44 := assump_2 assump_126
          apply False.elim assump_44
    case inr assump_7 =>
      cases assump_7
      case inl assump_58 =>
        cases assump_58
        case inl assump_60 =>
          apply Or.inl
          apply Or.inr
          intro assump_64
          have assump_127 : ((p6 ∧ True) → (p4 → p6)) := by
            intro assump_70
            intro assump_71
            cases assump_70
            case intro assump_74 assump_75 =>
              exact assump_74
          let assump_69 := assump_2 assump_127
          apply False.elim assump_69
        case inr assump_61 =>
          apply Or.inl
          apply Or.inr
          intro assump_85
          have assump_128 : ((p6 ∧ True) → (p4 → p6)) := by
            intro assump_91
            intro assump_92
            cases assump_91
            case intro assump_95 assump_96 =>
              exact assump_95
          let assump_90 := assump_2 assump_128
          apply False.elim assump_90
      case inr assump_59 =>
        apply Or.inl
        apply Or.inr
        intro assump_106
        have assump_129 : ((p6 ∧ True) → (p4 → p6)) := by
          intro assump_112
          intro assump_113
          cases assump_112
          case intro assump_116 assump_117 =>
            exact assump_116
        let assump_111 := assump_2 assump_129
        apply False.elim assump_111


variable (p1 p0 p5 p3 p4 p7 : Prop)
theorem file43_35023 : ((((((p3 → p5) → (p0 → True)) → ((True → False) ∧ (p5 ∧ p4))) → (((p3 ∧ p4) → (False → p1)) ∧ ((p4 → False) ∨ (p7 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p3 → p5) → (p0 → True)) → ((True → False) ∧ (p5 ∧ p4))) → (((p3 ∧ p4) → (False → p1)) ∧ ((p4 → False) ∨ (p7 ∨ p1)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    apply False.elim assump_7
    apply Or.inl
    intro assump_12
    have assump_28 : ((p3 → p5) → (p0 → True)) := by
      intro assump_17
      intro assump_18
      apply True.intro
    let assump_16 := assump_5 assump_28
    let assump_19 := And.left assump_16
    have assump_29 : True := by
      apply True.intro
    let assump_20 := assump_19 assump_29
    apply False.elim assump_20
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p0 p2 p6 p7 p4 p3 p1 : Prop)
theorem file43_35932 : (((((p7 → True) ∨ (p2 → False)) ∨ ((False ∨ p6) → False)) ∨ (((p0 → False) → (p2 → False)) → False)) ∨ ((((p2 → p4) → (p2 ∨ p4)) ∨ ((p3 → False) ∧ (p2 ∧ p1))) ∨ (((p0 ∧ False) → False) ∧ ((False ∨ p7) → (p0 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply True.intro


variable (p2 p1 p4 : Prop)
theorem file43_36305 : ((((((True ∨ p4) → (False → p1)) ∧ ((p2 ∧ p2) → False)) → (((p2 ∨ False) ∨ (False → False)) ∨ ((p2 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True ∨ p4) → (False → p1)) ∧ ((p2 ∧ p2) → False)) → (((p2 ∨ False) ∨ (False → False)) ∨ ((p2 → False) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inr
      intro assump_12
      apply False.elim assump_12
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p1 p0 : Prop)
theorem file43_36890 : (((((p4 → p4) → (p4 ∧ True)) → False) → False) → ((((p0 ∧ False) ∧ (True → False)) ∧ ((p4 → False) ∧ (True ∧ p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8


variable (p2 p7 p4 p1 p3 p5 p0 : Prop)
theorem file43_37317 : (((((p5 → p2) ∧ (p7 → False)) ∧ ((p0 ∧ p0) → False)) ∨ (((p2 ∧ True) ∧ (False → False)) ∧ ((p5 → True) ∧ (p2 ∨ p0)))) → ((((p4 ∨ p3) ∧ (True → False)) → False) ∨ (((p4 → True) → False) → ((p4 ∨ True) → (p1 ∨ p3))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            have assump_99 : True := by
              apply True.intro
            let assump_23 := assump_16 assump_99
            apply False.elim assump_23
          case inr assump_18 =>
            have assump_100 : True := by
              apply True.intro
            let assump_31 := assump_16 assump_100
            apply False.elim assump_31
  case inr assump_3 =>
    cases assump_3
    case intro assump_35 assump_36 =>
      cases assump_35
      case intro assump_37 assump_38 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          cases assump_36
          case intro assump_47 assump_48 =>
            cases assump_48
            case inl assump_51 =>
              apply Or.inl
              intro assump_55
              cases assump_55
              case intro assump_56 assump_57 =>
                cases assump_56
                case inl assump_58 =>
                  have assump_101 : True := by
                    apply True.intro
                  let assump_64 := assump_57 assump_101
                  apply False.elim assump_64
                case inr assump_59 =>
                  have assump_102 : True := by
                    apply True.intro
                  let assump_72 := assump_57 assump_102
                  apply False.elim assump_72
            case inr assump_52 =>
              apply Or.inl
              intro assump_78
              cases assump_78
              case intro assump_79 assump_80 =>
                cases assump_79
                case inl assump_81 =>
                  have assump_103 : True := by
                    apply True.intro
                  let assump_87 := assump_80 assump_103
                  apply False.elim assump_87
                case inr assump_82 =>
                  have assump_104 : True := by
                    apply True.intro
                  let assump_95 := assump_80 assump_104
                  apply False.elim assump_95


variable (p2 p5 p3 p6 p4 p1 p7 : Prop)
theorem file43_39894 : ((((((p7 → False) → (False → p1)) → ((p5 ∧ p2) → (p2 → p5))) ∨ (((p4 → True) → (p3 → p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p7 → False) → (False → p1)) → ((p5 ∧ p2) → (p2 → p5))) ∨ (((p4 → True) → (p3 → p6)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      exact assump_10
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p3 p0 p6 p2 p4 p7 p5 p1 : Prop)
theorem file43_40442 : (((((p3 ∨ p5) ∨ (p7 → True)) → False) → (((p0 → p7) ∧ (p6 → False)) ∧ ((False → False) ∨ (p4 → p2)))) ∨ ((((p2 → False) ∨ (p0 ∧ False)) → False) ∧ (((p0 → False) ∨ (p0 → False)) ∧ ((p2 → False) ∧ (True ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_27 : ((p3 ∨ p5) ∨ (p7 → True)) := by
    apply Or.inr
    intro assump_8
    apply True.intro
  let assump_7 := assump_1 assump_27
  apply False.elim assump_7
  intro assump_12
  have assump_28 : ((p3 ∨ p5) ∨ (p7 → True)) := by
    apply Or.inr
    intro assump_18
    apply True.intro
  let assump_17 := assump_1 assump_28
  apply False.elim assump_17
  apply Or.inl
  intro assump_24
  apply False.elim assump_24


variable (p3 p4 p7 p5 p6 p0 p1 : Prop)
theorem file43_41237 : (((((p0 → False) ∨ (True → False)) → ((p4 → False) ∧ (p7 ∧ p4))) ∧ (((False ∧ p1) → False) → False)) → ((((True → p5) → (True → p4)) ∧ ((p6 ∧ p4) ∨ (p3 ∧ p0))) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case inl assump_11 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_5
        case intro assump_19 assump_20 =>
          have assump_55 : ((False ∧ p1) → False) := by
            intro assump_26
            cases assump_26
            case intro assump_27 assump_28 =>
              apply False.elim assump_27
          let assump_25 := assump_20 assump_55
          apply False.elim assump_25
    case inr assump_12 =>
      cases assump_12
      case intro assump_34 assump_35 =>
        cases assump_5
        case intro assump_40 assump_41 =>
          have assump_56 : ((False ∧ p1) → False) := by
            intro assump_47
            cases assump_47
            case intro assump_48 assump_49 =>
              apply False.elim assump_48
          let assump_46 := assump_41 assump_56
          apply False.elim assump_46


variable (p6 p2 p4 p7 p3 p1 p0 : Prop)
theorem file43_42452 : ((((((p4 ∧ p4) ∧ (p3 → p2)) ∧ ((p6 → p2) → (True ∨ p2))) → (((p3 ∧ False) ∧ (p4 ∧ True)) ∨ ((False → False) ∧ (p0 ∨ p7)))) ∧ ((((p1 → p2) → (False → p1)) ∨ ((p6 ∧ False) ∨ (p1 ∧ p4))) ∧ (((p4 ∨ p7) → (p7 ∧ p2)) ∧ ((False → False) → (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          have assump_54 : (False → False) := by
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_13 assump_54
          have assump_55 : True := by
            apply True.intro
          let assump_22 := assump_18 assump_55
          apply False.elim assump_22
      case inr assump_9 =>
        cases assump_9
        case inl assump_26 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_29
        case inr assump_27 =>
          cases assump_27
          case intro assump_34 assump_35 =>
            cases assump_7
            case intro assump_40 assump_41 =>
              have assump_56 : (False → False) := by
                intro assump_47
                apply False.elim assump_47
              let assump_46 := assump_41 assump_56
              have assump_57 : True := by
                apply True.intro
              let assump_50 := assump_46 assump_57
              apply False.elim assump_50


variable (p3 p4 p1 p0 p6 p7 p2 : Prop)
theorem file43_44039 : (((((p3 → False) ∨ (p1 ∧ False)) ∧ ((True ∧ p7) ∨ (p0 → p0))) ∧ (((p7 → False) → (p3 → p3)) → False)) → ((((p2 ∧ p0) → (p4 ∨ False)) ∧ ((p0 ∧ p3) → False)) → (((p4 → False) → (p0 → p4)) → ((p1 ∨ True) ∧ (p6 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              apply Or.inr
              apply True.intro
          case inr assump_21 =>
            apply Or.inr
            apply True.intro
        case inr assump_17 =>
          cases assump_17
          case intro assump_34 assump_35 =>
            apply False.elim assump_35
  intro assump_40
  cases assump_2
  case intro assump_45 assump_46 =>
    cases assump_1
    case intro assump_51 assump_52 =>
      cases assump_51
      case intro assump_53 assump_54 =>
        cases assump_53
        case inl assump_55 =>
          cases assump_54
          case inl assump_59 =>
            cases assump_59
            case intro assump_61 assump_62 =>
              have assump_99 : ((p7 → False) → (p3 → p3)) := by
                intro assump_70
                intro assump_71
                exact assump_71
              let assump_69 := assump_52 assump_99
              apply False.elim assump_69
          case inr assump_60 =>
            have assump_100 : ((p7 → False) → (p3 → p3)) := by
              intro assump_84
              intro assump_85
              exact assump_85
            let assump_83 := assump_52 assump_100
            apply False.elim assump_83
        case inr assump_56 =>
          cases assump_56
          case intro assump_93 assump_94 =>
            apply False.elim assump_94


variable (p1 p5 p0 p3 p6 p2 p7 : Prop)
theorem file43_46077 : ((((((p1 ∧ p1) → (p2 → False)) ∧ ((p5 → False) → False)) ∧ (((p2 ∨ p0) ∧ (True ∧ p0)) ∧ ((p2 ∧ p5) ∨ (p2 ∧ p3)))) ∧ ((((p7 → False) → False) ∧ ((False → False) → False)) ∧ (((p7 → False) ∧ (p6 ∧ p3)) ∨ ((p1 → True) → False)))) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_22
        case intro assump_29 assump_30 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            cases assump_31
            case inl assump_33 =>
              cases assump_32
              case intro assump_37 assump_38 =>
                cases assump_30
                case inl assump_43 =>
                  cases assump_43
                  case intro assump_45 assump_46 =>
                    cases assump_20
                    case intro assump_51 assump_52 =>
                      cases assump_51
                      case intro assump_53 assump_54 =>
                        cases assump_52
                        case inl assump_59 =>
                          cases assump_59
                          case intro assump_61 assump_62 =>
                            cases assump_62
                            case intro assump_65 assump_66 =>
                              have assump_227 : (False → False) := by
                                intro assump_75
                                apply False.elim assump_75
                              let assump_74 := assump_54 assump_227
                              apply False.elim assump_74
                        case inr assump_60 =>
                          have assump_228 : (p1 → True) := by
                            intro assump_84
                            apply True.intro
                          let assump_83 := assump_60 assump_228
                          apply False.elim assump_83
                case inr assump_44 =>
                  cases assump_44
                  case intro assump_88 assump_89 =>
                    cases assump_20
                    case intro assump_94 assump_95 =>
                      cases assump_94
                      case intro assump_96 assump_97 =>
                        cases assump_95
                        case inl assump_102 =>
                          cases assump_102
                          case intro assump_104 assump_105 =>
                            cases assump_105
                            case intro assump_108 assump_109 =>
                              have assump_229 : (False → False) := by
                                intro assump_118
                                apply False.elim assump_118
                              let assump_117 := assump_97 assump_229
                              apply False.elim assump_117
                        case inr assump_103 =>
                          have assump_230 : (p1 → True) := by
                            intro assump_127
                            apply True.intro
                          let assump_126 := assump_103 assump_230
                          apply False.elim assump_126
            case inr assump_34 =>
              cases assump_32
              case intro assump_133 assump_134 =>
                cases assump_30
                case inl assump_139 =>
                  cases assump_139
                  case intro assump_141 assump_142 =>
                    cases assump_20
                    case intro assump_147 assump_148 =>
                      cases assump_147
                      case intro assump_149 assump_150 =>
                        cases assump_148
                        case inl assump_155 =>
                          cases assump_155
                          case intro assump_157 assump_158 =>
                            cases assump_158
                            case intro assump_161 assump_162 =>
                              have assump_231 : (False → False) := by
                                intro assump_171
                                apply False.elim assump_171
                              let assump_170 := assump_150 assump_231
                              apply False.elim assump_170
                        case inr assump_156 =>
                          have assump_232 : (p1 → True) := by
                            intro assump_180
                            apply True.intro
                          let assump_179 := assump_156 assump_232
                          apply False.elim assump_179
                case inr assump_140 =>
                  cases assump_140
                  case intro assump_184 assump_185 =>
                    cases assump_20
                    case intro assump_190 assump_191 =>
                      cases assump_190
                      case intro assump_192 assump_193 =>
                        cases assump_191
                        case inl assump_198 =>
                          cases assump_198
                          case intro assump_200 assump_201 =>
                            cases assump_201
                            case intro assump_204 assump_205 =>
                              have assump_233 : (False → False) := by
                                intro assump_214
                                apply False.elim assump_214
                              let assump_213 := assump_193 assump_233
                              apply False.elim assump_213
                        case inr assump_199 =>
                          have assump_234 : (p1 → True) := by
                            intro assump_223
                            apply True.intro
                          let assump_222 := assump_199 assump_234
                          apply False.elim assump_222


variable (p3 p5 p4 p1 p7 p2 p6 p0 : Prop)
theorem file43_51973 : ((((((p2 ∧ p0) → (p0 → p7)) ∧ ((p3 → False) ∨ (p4 → p5))) → (((p6 → False) ∧ (p1 ∨ p1)) ∧ ((p7 → False) → False))) ∧ ((((p6 → False) → (False → p1)) ∨ ((p7 ∧ p5) → False)) ∧ (((False → False) ∨ (p4 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_32 : ((False → False) ∨ (p4 → False)) := by
          apply Or.inl
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_7 assump_32
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_33 : ((False → False) ∨ (p4 → False)) := by
          apply Or.inl
          intro assump_26
          apply False.elim assump_26
        let assump_25 := assump_7 assump_33
        apply False.elim assump_25


variable (p2 p7 p6 p3 p4 p1 p5 : Prop)
theorem file43_52926 : ((((((p6 → False) → False) ∧ ((p5 ∨ p4) → False)) → (((p4 → True) → False) → False)) ∧ ((((p4 → False) ∨ (p2 → p7)) ∨ ((p6 ∨ p1) ∧ (p5 → False))) ∧ (((p1 ∨ p4) ∧ (p1 ∧ p3)) ∧ ((p3 ∨ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_17
                case intro assump_22 assump_23 =>
                  have assump_164 : (p3 ∨ p6) := by
                    apply Or.inl
                    exact assump_23
                  let assump_30 := assump_15 assump_164
                  apply False.elim assump_30
              case inr assump_19 =>
                cases assump_17
                case intro assump_36 assump_37 =>
                  have assump_165 : (p3 ∨ p6) := by
                    apply Or.inl
                    exact assump_37
                  let assump_44 := assump_15 assump_165
                  apply False.elim assump_44
        case inr assump_11 =>
          cases assump_7
          case intro assump_50 assump_51 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_52
              case inl assump_54 =>
                cases assump_53
                case intro assump_58 assump_59 =>
                  have assump_166 : (p3 ∨ p6) := by
                    apply Or.inl
                    exact assump_59
                  let assump_66 := assump_51 assump_166
                  apply False.elim assump_66
              case inr assump_55 =>
                cases assump_53
                case intro assump_72 assump_73 =>
                  have assump_167 : (p3 ∨ p6) := by
                    apply Or.inl
                    exact assump_73
                  let assump_80 := assump_51 assump_167
                  apply False.elim assump_80
      case inr assump_9 =>
        cases assump_9
        case intro assump_84 assump_85 =>
          cases assump_84
          case inl assump_86 =>
            cases assump_7
            case intro assump_92 assump_93 =>
              cases assump_92
              case intro assump_94 assump_95 =>
                cases assump_94
                case inl assump_96 =>
                  cases assump_95
                  case intro assump_100 assump_101 =>
                    have assump_168 : (p3 ∨ p6) := by
                      apply Or.inl
                      exact assump_101
                    let assump_108 := assump_93 assump_168
                    apply False.elim assump_108
                case inr assump_97 =>
                  cases assump_95
                  case intro assump_114 assump_115 =>
                    have assump_169 : (p3 ∨ p6) := by
                      apply Or.inl
                      exact assump_115
                    let assump_122 := assump_93 assump_169
                    apply False.elim assump_122
          case inr assump_87 =>
            cases assump_7
            case intro assump_130 assump_131 =>
              cases assump_130
              case intro assump_132 assump_133 =>
                cases assump_132
                case inl assump_134 =>
                  cases assump_133
                  case intro assump_138 assump_139 =>
                    have assump_170 : (p3 ∨ p6) := by
                      apply Or.inl
                      exact assump_139
                    let assump_146 := assump_131 assump_170
                    apply False.elim assump_146
                case inr assump_135 =>
                  cases assump_133
                  case intro assump_152 assump_153 =>
                    have assump_171 : (p3 ∨ p6) := by
                      apply Or.inl
                      exact assump_153
                    let assump_160 := assump_131 assump_171
                    apply False.elim assump_160


variable (p4 p0 p6 p3 p5 p7 : Prop)
theorem file43_57163 : ((((((p4 → True) → False) → ((True ∧ p5) → False)) ∨ (((p6 → p7) ∨ (p3 → False)) ∨ ((p0 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p4 → True) → False) → ((True ∧ p5) → False)) ∨ (((p6 → p7) ∨ (p3 → False)) ∨ ((p0 → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_24 : (p4 → True) := by
        intro assump_16
        apply True.intro
      let assump_15 := assump_5 assump_24
      apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p0 p3 p6 p4 p1 p5 p7 p2 : Prop)
theorem file43_57849 : (((((p0 ∨ True) → (True ∨ p0)) ∨ ((p2 ∧ p7) → (True → False))) → (((p7 ∨ p7) ∧ (False ∨ p6)) ∨ ((False → False) ∨ (p7 → False)))) ∨ ((((p1 ∨ p2) → False) ∨ ((True ∧ p3) ∧ (False → p4))) → (((p5 ∧ p7) → (False → True)) → False))) := by
  apply Or.inl
  intro assump_25
  cases assump_25
  case inl assump_26 =>
    apply Or.inr
    apply Or.inl
    intro assump_30
    apply False.elim assump_30
  case inr assump_27 =>
    apply Or.inr
    apply Or.inl
    intro assump_35
    apply False.elim assump_35


variable (p7 p0 p6 p4 p3 p1 p5 : Prop)
theorem file43_58416 : (((((False → False) → False) ∧ ((True → False) ∨ (p5 ∨ p0))) ∨ (((True ∨ p7) → False) ∧ ((False → False) → (p6 ∧ p1)))) → ((((True ∧ p4) → False) → False) → (((p6 → p3) ∨ (p1 → False)) ∧ ((True ∨ False) ∨ (p5 ∨ p6))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        apply Or.inl
        intro assump_15
        have assump_98 : True := by
          apply True.intro
        let assump_19 := assump_11 assump_98
        apply False.elim assump_19
      case inr assump_12 =>
        cases assump_12
        case inl assump_23 =>
          apply Or.inl
          intro assump_27
          have assump_99 : (False → False) := by
            intro assump_33
            apply False.elim assump_33
          let assump_32 := assump_7 assump_99
          apply False.elim assump_32
        case inr assump_24 =>
          apply Or.inl
          intro assump_41
          have assump_100 : (False → False) := by
            intro assump_47
            apply False.elim assump_47
          let assump_46 := assump_7 assump_100
          apply False.elim assump_46
  case inr assump_6 =>
    cases assump_6
    case intro assump_53 assump_54 =>
      apply Or.inl
      intro assump_59
      have assump_101 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_70 := assump_53 assump_101
      apply False.elim assump_70
  cases assump_1
  case inl assump_76 =>
    cases assump_76
    case intro assump_78 assump_79 =>
      cases assump_79
      case inl assump_82 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_83 =>
        cases assump_83
        case inl assump_86 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_87 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
  case inr assump_77 =>
    cases assump_77
    case intro assump_92 assump_93 =>
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p7 p2 p6 p3 p1 p0 p5 : Prop)
theorem file43_60601 : ((((((p3 → False) → False) ∧ ((True ∨ p3) → False)) → (((p5 ∨ p6) → (p1 ∧ p7)) ∨ ((p0 ∧ p1) → (p2 → p7)))) → False) → False) := by
  intro assump_1
  have assump_48 : ((((p3 → False) → False) ∧ ((True ∨ p3) → False)) → (((p5 ∨ p6) → (p1 ∧ p7)) ∨ ((p0 ∧ p1) → (p2 → p7)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      apply And.intro
      cases assump_12
      case inl assump_13 =>
        have assump_49 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_18 := assump_7 assump_49
        apply False.elim assump_18
      case inr assump_14 =>
        have assump_50 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_25 := assump_7 assump_50
        apply False.elim assump_25
      cases assump_12
      case inl assump_29 =>
        have assump_51 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_34 := assump_7 assump_51
        apply False.elim assump_34
      case inr assump_30 =>
        have assump_52 : (True ∨ p3) := by
          apply Or.inl
          apply True.intro
        let assump_41 := assump_7 assump_52
        apply False.elim assump_41
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p4 p3 p1 p6 p2 : Prop)
theorem file43_61982 : ((((((p3 ∨ p4) ∨ (p6 ∧ p2)) → False) → (((True → False) ∧ (p1 → False)) → ((p2 ∧ True) ∧ (p3 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_52 : ((((p3 ∨ p4) ∨ (p6 ∧ p2)) → False) → (((True → False) ∧ (p1 → False)) → ((p2 ∧ True) ∧ (p3 ∧ p3)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_53 : True := by
        apply True.intro
      let assump_17 := assump_7 assump_53
      apply False.elim assump_17
    apply True.intro
    apply And.intro
    cases assump_6
    case intro assump_21 assump_22 =>
      have assump_54 : True := by
        apply True.intro
      let assump_31 := assump_21 assump_54
      apply False.elim assump_31
    cases assump_6
    case intro assump_35 assump_36 =>
      have assump_55 : True := by
        apply True.intro
      let assump_45 := assump_35 assump_55
      apply False.elim assump_45
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4


variable (p2 p1 p5 p3 p6 p0 p4 : Prop)
theorem file43_63070 : ((((((p2 → True) ∧ (p5 ∨ p6)) ∧ ((p4 ∧ True) → (p0 → p6))) ∨ (((p3 → False) → (False ∨ True)) ∨ ((p4 ∧ p4) → False))) ∧ ((((p5 → False) ∨ (p3 ∧ p4)) → ((p3 ∨ False) ∨ (p6 → p4))) ∧ (((p1 → p4) → (p0 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case inl assump_12 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              have assump_76 : ((p1 → p4) → (p0 → True)) := by
                intro assump_25
                intro assump_26
                apply True.intro
              let assump_24 := assump_19 assump_76
              apply False.elim assump_24
          case inr assump_13 =>
            cases assump_3
            case intro assump_34 assump_35 =>
              have assump_77 : ((p1 → p4) → (p0 → True)) := by
                intro assump_41
                intro assump_42
                apply True.intro
              let assump_40 := assump_35 assump_77
              apply False.elim assump_40
    case inr assump_5 =>
      cases assump_5
      case inl assump_46 =>
        cases assump_3
        case intro assump_50 assump_51 =>
          have assump_78 : ((p1 → p4) → (p0 → True)) := by
            intro assump_57
            intro assump_58
            apply True.intro
          let assump_56 := assump_51 assump_78
          apply False.elim assump_56
      case inr assump_47 =>
        cases assump_3
        case intro assump_64 assump_65 =>
          have assump_79 : ((p1 → p4) → (p0 → True)) := by
            intro assump_71
            intro assump_72
            apply True.intro
          let assump_70 := assump_65 assump_79
          apply False.elim assump_70


variable (p5 p0 p6 p1 p2 p7 p3 p4 : Prop)
theorem file43_65031 : (((((p0 ∧ p3) ∨ (p1 → p1)) → False) → (((p3 ∨ p4) → (p5 ∧ p0)) → False)) ∨ ((((False ∨ False) ∧ (p3 → False)) ∨ ((p4 ∧ p2) → False)) ∨ (((p6 ∧ p3) → (True → False)) ∧ ((p3 ∨ True) ∧ (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_14 : ((p0 ∧ p3) ∨ (p1 → p1)) := by
    apply Or.inr
    intro assump_8
    exact assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p7 p2 p0 p4 p3 p5 p1 p6 : Prop)
theorem file43_65520 : ((((((p5 → True) ∨ (p7 ∧ p0)) → ((False → False) → False)) ∧ (((p4 ∨ p4) ∨ (p6 ∧ p5)) ∨ ((False ∨ p2) ∨ (p3 → False)))) ∨ ((((p1 ∨ p6) ∨ (p3 ∨ p5)) → ((p5 → p0) ∨ (p4 → p2))) ∧ (((p1 ∧ p4) → (False → False)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_14
          case inl assump_16 =>
            have assump_103 : ((p5 → True) ∨ (p7 ∧ p0)) := by
              apply Or.inl
              intro assump_22
              apply True.intro
            let assump_21 := assump_8 assump_103
            have assump_104 : (False → False) := by
              intro assump_24
              apply False.elim assump_24
            let assump_23 := assump_21 assump_104
            apply False.elim assump_23
          case inr assump_17 =>
            have assump_105 : ((p5 → True) ∨ (p7 ∧ p0)) := by
              apply Or.inl
              intro assump_34
              apply True.intro
            let assump_33 := assump_8 assump_105
            have assump_106 : (False → False) := by
              intro assump_36
              apply False.elim assump_36
            let assump_35 := assump_33 assump_106
            apply False.elim assump_35
        case inr assump_15 =>
          cases assump_15
          case intro assump_42 assump_43 =>
            have assump_107 : ((p5 → True) ∨ (p7 ∧ p0)) := by
              apply Or.inl
              intro assump_51
              apply True.intro
            let assump_50 := assump_8 assump_107
            have assump_108 : (False → False) := by
              intro assump_53
              apply False.elim assump_53
            let assump_52 := assump_50 assump_108
            apply False.elim assump_52
      case inr assump_13 =>
        cases assump_13
        case inl assump_59 =>
          cases assump_59
          case inl assump_61 =>
            apply False.elim assump_61
          case inr assump_62 =>
            have assump_109 : ((p5 → True) ∨ (p7 ∧ p0)) := by
              apply Or.inl
              intro assump_69
              apply True.intro
            let assump_68 := assump_8 assump_109
            have assump_110 : (False → False) := by
              intro assump_71
              apply False.elim assump_71
            let assump_70 := assump_68 assump_110
            apply False.elim assump_70
        case inr assump_60 =>
          have assump_111 : ((p5 → True) ∨ (p7 ∧ p0)) := by
            apply Or.inl
            intro assump_81
            apply True.intro
          let assump_80 := assump_8 assump_111
          have assump_112 : (False → False) := by
            intro assump_83
            apply False.elim assump_83
          let assump_82 := assump_80 assump_112
          apply False.elim assump_82
  case inr assump_7 =>
    cases assump_7
    case intro assump_89 assump_90 =>
      have assump_113 : ((p1 ∧ p4) → (False → False)) := by
        intro assump_96
        intro assump_97
        apply False.elim assump_97
      let assump_95 := assump_90 assump_113
      apply False.elim assump_95


variable (p7 p3 p6 p2 p1 : Prop)
theorem file43_68792 : ((((((False ∧ p1) → (True → False)) → ((p7 → p3) → False)) → (((p6 ∧ p6) ∨ (p6 ∧ True)) ∨ ((p2 ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_36 : ((((False ∧ p1) → (True → False)) → ((p7 → p3) → False)) → (((p6 ∧ p6) ∨ (p6 ∧ True)) ∨ ((p2 ∧ p3) → False))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_37 : ((False ∧ p1) → (True → False)) := by
        intro assump_18
        intro assump_19
        cases assump_18
        case intro assump_22 assump_23 =>
          apply False.elim assump_22
      let assump_17 := assump_5 assump_37
      have assump_38 : (p7 → p3) := by
        intro assump_27
        exact assump_10
      let assump_26 := assump_17 assump_38
      apply False.elim assump_26
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p7 p2 p4 p3 p6 p0 p5 : Prop)
theorem file43_69736 : ((((((p7 ∨ False) → False) → ((False ∧ p5) → (True → p6))) ∧ (((p6 ∨ p2) ∧ (p5 → p3)) ∨ ((p5 ∨ p7) → (p7 ∧ True)))) ∧ ((((True ∨ p0) → (p4 ∨ p2)) ∧ ((p5 → False) ∧ (False ∧ False))) ∧ (((p5 ∨ p4) ∨ (True → False)) → False))) → False) := by
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
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case intro assump_28 assump_29 =>
                    apply False.elim assump_28
          case inr assump_13 =>
            cases assump_3
            case intro assump_36 assump_37 =>
              cases assump_36
              case intro assump_38 assump_39 =>
                cases assump_39
                case intro assump_42 assump_43 =>
                  cases assump_43
                  case intro assump_46 assump_47 =>
                    apply False.elim assump_46
      case inr assump_9 =>
        cases assump_3
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_55
            case intro assump_58 assump_59 =>
              cases assump_59
              case intro assump_62 assump_63 =>
                apply False.elim assump_62


variable (p6 p5 p7 p3 : Prop)
theorem file43_71445 : (((((p3 → p7) ∧ (p3 → False)) → False) ∧ (((p3 ∨ p5) → (p3 ∨ True)) → ((True ∨ p6) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : ((p3 ∨ p5) → (p3 ∨ True)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        exact assump_10
      case inr assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_3 assump_20
    have assump_21 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_16 := assump_8 assump_21
    apply False.elim assump_16


variable (p6 p0 p7 p3 p2 : Prop)
theorem file43_72112 : ((((((p2 → False) → False) ∨ ((p2 → False) → False)) → False) ∧ ((((True ∧ True) ∨ (p6 ∨ p2)) → False) ∧ (((p3 → True) ∨ (p7 → p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : ((p3 → True) ∨ (p7 → p0)) := by
        apply Or.inl
        intro assump_13
        apply True.intro
      let assump_12 := assump_7 assump_17
      apply False.elim assump_12


variable (p5 p1 : Prop)
theorem file43_72641 : ((((((False → False) → False) ∧ ((p1 ∧ True) ∨ (p5 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_39 : ((((False → False) → False) ∧ ((p1 ∧ True) ∨ (p5 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_40 : (False → False) := by
            intro assump_20
            apply False.elim assump_20
          let assump_19 := assump_6 assump_40
          apply False.elim assump_19
      case inr assump_11 =>
        have assump_41 : (False → False) := by
          intro assump_30
          apply False.elim assump_30
        let assump_29 := assump_6 assump_41
        apply False.elim assump_29
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p7 p2 p6 p3 p4 p0 p5 : Prop)
theorem file43_73580 : (((((True → p6) ∨ (p2 → p7)) → ((p3 → True) ∨ (p0 ∨ True))) ∨ (((True ∨ True) → (p0 ∨ p4)) ∧ ((p4 ∧ p2) ∨ (p5 ∧ p5)))) ∨ ((((p4 ∨ p2) → False) ∧ ((p3 ∧ p6) → False)) ∨ (((p5 ∨ p7) ∧ (p4 ∨ p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    intro assump_9
    apply True.intro


variable (p4 p2 : Prop)
theorem file43_74062 : (((((p2 ∨ p2) ∧ (True → False)) → ((p4 ∨ False) → False)) → False) → ((((p2 → False) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_39 : (((p2 ∨ p2) ∧ (True → False)) → ((p4 ∨ False) → False)) := by
    intro assump_8
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      cases assump_8
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          have assump_40 : True := by
            apply True.intro
          let assump_22 := assump_15 assump_40
          apply False.elim assump_22
        case inr assump_17 =>
          have assump_41 : True := by
            apply True.intro
          let assump_30 := assump_15 assump_41
          apply False.elim assump_30
    case inr assump_11 =>
      apply False.elim assump_11
  let assump_7 := assump_1 assump_39
  apply False.elim assump_7


variable (p6 p3 p2 p7 p0 p4 p5 : Prop)
theorem file43_75013 : ((((((p7 ∨ p2) ∨ (p5 → p2)) ∧ ((False → True) ∨ (p2 ∨ p3))) → (((p6 → False) ∧ (p6 → False)) ∨ ((p6 ∧ p4) → (p2 → False)))) ∧ ((((p4 → p6) → (p3 → p3)) ∧ ((p6 ∧ p0) → False)) ∧ (((p2 ∨ p7) ∨ (p0 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_20 : ((p2 ∨ p7) ∨ (p0 ∨ True)) := by
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_16 := assump_7 assump_20
        apply False.elim assump_16


variable (p2 p7 p6 p1 p0 p5 p3 p4 : Prop)
theorem file43_75700 : ((((((p3 → p7) ∧ (p5 ∧ p3)) → False) ∧ (((False ∨ False) ∧ (p3 → p0)) ∨ ((True → p7) ∧ (p1 ∨ p2)))) ∧ ((((p3 → p6) ∨ (p3 ∨ p4)) → ((p1 → False) ∧ (p2 ∨ p0))) ∧ (((p0 ∨ p2) ∨ (p4 ∨ True)) → False))) → False) := by
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
            apply False.elim assump_12
          case inr assump_13 =>
            apply False.elim assump_13
      case inr assump_9 =>
        cases assump_9
        case intro assump_18 assump_19 =>
          cases assump_19
          case inl assump_22 =>
            cases assump_3
            case intro assump_26 assump_27 =>
              have assump_48 : ((p0 ∨ p2) ∨ (p4 ∨ True)) := by
                apply Or.inr
                apply Or.inr
                apply True.intro
              let assump_32 := assump_27 assump_48
              apply False.elim assump_32
          case inr assump_23 =>
            cases assump_3
            case intro assump_38 assump_39 =>
              have assump_49 : ((p0 ∨ p2) ∨ (p4 ∨ True)) := by
                apply Or.inl
                apply Or.inr
                exact assump_23
              let assump_44 := assump_39 assump_49
              apply False.elim assump_44


variable (p6 p4 p5 p7 p2 p0 p3 : Prop)
theorem file43_77199 : (((((p2 ∨ p0) → (p7 → True)) → False) → (((p4 ∨ True) → False) → ((False → p6) ∧ (p5 → False)))) ∨ ((((p5 ∨ p3) ∧ (p6 ∨ p5)) ∨ ((False ∨ p3) ∨ (p5 ∨ p0))) ∧ (((p0 ∧ p0) → (True → False)) ∨ ((False ∧ p7) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  have assump_19 : ((p2 ∨ p0) → (p7 → True)) := by
    intro assump_14
    intro assump_15
    apply True.intro
  let assump_13 := assump_1 assump_19
  apply False.elim assump_13


variable (p7 p4 p5 p3 p2 : Prop)
theorem file43_77785 : ((((((p2 ∨ p7) → False) ∨ ((True ∨ False) → (p2 ∨ p5))) → False) ∧ ((((p3 ∨ False) → (False → p4)) ∨ ((p2 → p7) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p3 ∨ False) → (False → p4)) ∨ ((p2 → p7) → False)) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p5 p0 p4 p1 : Prop)
theorem file43_78299 : ((((((p0 → False) ∨ (p1 ∧ p4)) → ((p5 → False) → (p5 → False))) ∧ (((True → False) ∧ (p0 ∧ True)) → ((p5 ∧ True) → False))) → False) → False) := by
  intro assump_10
  have assump_68 : ((((p0 → False) ∨ (p1 ∧ p4)) → ((p5 → False) → (p5 → False))) ∧ (((True → False) ∧ (p0 ∧ True)) → ((p5 ∧ True) → False))) := by
    apply And.intro
    intro assump_14
    intro assump_15
    intro assump_16
    cases assump_14
    case inl assump_21 =>
      have assump_69 : p5 := by
        exact assump_16
      let assump_26 := assump_15 assump_69
      apply False.elim assump_26
    case inr assump_22 =>
      cases assump_22
      case intro assump_30 assump_31 =>
        have assump_70 : p5 := by
          exact assump_16
        let assump_38 := assump_15 assump_70
        apply False.elim assump_38
    intro assump_42
    intro assump_43
    cases assump_43
    case intro assump_44 assump_45 =>
      cases assump_42
      case intro assump_50 assump_51 =>
        cases assump_51
        case intro assump_54 assump_55 =>
          have assump_71 : True := by
            apply True.intro
          let assump_61 := assump_50 assump_71
          apply False.elim assump_61
  let assump_13 := assump_10 assump_68
  apply False.elim assump_13


variable (p5 p4 p1 p2 p3 : Prop)
theorem file43_79600 : ((((((True ∨ p2) ∨ (p4 → p3)) ∨ ((p4 ∧ False) → False)) ∨ (((True → False) ∧ (False ∨ p1)) → ((p5 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ p2) ∨ (p4 → p3)) ∨ ((p4 ∧ False) → False)) ∨ (((True → False) ∧ (False ∨ p1)) → ((p5 → False) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p6 p7 p4 : Prop)
theorem file43_80106 : (((((False → False) ∧ (p4 → False)) → ((p6 → True) ∨ (p2 ∨ p7))) → False) → False) := by
  intro assump_1
  have assump_16 : (((False → False) ∧ (p4 → False)) → ((p6 → True) ∨ (p2 ∨ p7))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      apply True.intro
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p3 p1 p5 p6 p2 : Prop)
theorem file43_80563 : ((((((p1 ∧ False) ∨ (True ∧ p1)) → ((p5 → p3) → (False ∨ p1))) → False) ∧ ((((p6 → True) → False) → ((p2 → False) ∨ (p0 → p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p6 → True) → False) → ((p2 → False) ∨ (p0 → p5))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      have assump_25 : (p6 → True) := by
        intro assump_17
        apply True.intro
      let assump_16 := assump_9 assump_25
      apply False.elim assump_16
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p2 p5 p4 p3 p0 p7 : Prop)
theorem file43_81220 : ((((((p0 → p5) → (p3 → p3)) ∨ ((p4 ∨ p5) → (p4 → p3))) → False) ∧ ((((p2 ∧ p5) ∧ (p5 → False)) → ((p7 → True) → (p2 → False))) → False)) → False) := by
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    have assump_61 : (((p2 ∧ p5) ∧ (p5 → False)) → ((p7 → True) → (p2 → False))) := by
      intro assump_37
      intro assump_38
      intro assump_39
      cases assump_37
      case intro assump_44 assump_45 =>
        cases assump_44
        case intro assump_46 assump_47 =>
          have assump_62 : p5 := by
            exact assump_47
          let assump_54 := assump_45 assump_62
          apply False.elim assump_54
    let assump_36 := assump_31 assump_61
    apply False.elim assump_36


variable (p0 p5 : Prop)
theorem file43_81993 : (((((False → False) → False) → ((p0 → False) ∧ (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_33 : (((False → False) → False) → ((p0 → False) ∧ (p5 → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_34 : (False → False) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_5 assump_34
    apply False.elim assump_11
    intro assump_18
    have assump_35 : (False → False) := by
      intro assump_24
      apply False.elim assump_24
    let assump_23 := assump_5 assump_35
    apply False.elim assump_23
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p6 p4 p7 p3 p0 p1 p5 : Prop)
theorem file43_82725 : (((((p5 ∧ p7) → False) → ((False → True) ∨ (False → p6))) ∨ (((p0 → False) ∨ (False → False)) → ((p6 → p4) → (p3 → False)))) ∨ ((((p5 → False) → (p4 ∧ p0)) ∨ ((p3 → False) → False)) ∧ (((p1 → True) ∧ (False → False)) ∨ ((False → p5) ∧ (p5 ∧ p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p7 p4 p3 p2 p1 p0 p6 p5 : Prop)
theorem file43_83144 : ((((((p0 → p0) → False) ∨ ((p5 → False) ∨ (p0 ∨ p3))) → (((False → False) → (p2 ∨ p0)) ∧ ((p6 ∨ p3) → (p1 → p6)))) ∧ ((((p7 ∨ p2) → False) ∧ ((True ∨ True) ∨ (p7 ∧ False))) ∧ (((False → False) ∨ (p7 ∨ p4)) → False))) → False) := by
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
            have assump_44 : ((False → False) ∨ (p7 ∨ p4)) := by
              apply Or.inl
              intro assump_21
              apply False.elim assump_21
            let assump_20 := assump_7 assump_44
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_45 : ((False → False) ∨ (p7 ∨ p4)) := by
              apply Or.inl
              intro assump_32
              apply False.elim assump_32
            let assump_31 := assump_7 assump_45
            apply False.elim assump_31
        case inr assump_13 =>
          cases assump_13
          case intro assump_38 assump_39 =>
            apply False.elim assump_39


variable (p3 p1 p7 p6 p4 : Prop)
theorem file43_84397 : (((((False ∨ p4) ∧ (False ∧ p1)) → False) → False) → ((((p3 → False) → False) ∨ ((p1 ∧ p7) → False)) ∨ (((p6 ∨ p1) → (p4 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_25 : (((False ∨ p4) ∧ (False ∧ p1)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        apply False.elim assump_12
      case inr assump_13 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
  let assump_8 := assump_1 assump_25
  apply False.elim assump_8


variable (p1 p4 p3 p6 : Prop)
theorem file43_85085 : (((((p6 ∨ p3) ∧ (True → False)) → ((p1 ∧ p4) ∨ (p4 → False))) → False) → False) := by
  intro assump_8
  have assump_44 : (((p6 ∨ p3) ∧ (True → False)) → ((p1 ∧ p4) ∨ (p4 → False))) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        apply Or.inr
        intro assump_21
        have assump_45 : True := by
          apply True.intro
        let assump_25 := assump_14 assump_45
        apply False.elim assump_25
      case inr assump_16 =>
        apply Or.inr
        intro assump_33
        have assump_46 : True := by
          apply True.intro
        let assump_37 := assump_14 assump_46
        apply False.elim assump_37
  let assump_11 := assump_8 assump_44
  apply False.elim assump_11


variable (p2 p7 p5 p1 p0 p4 p6 p3 : Prop)
theorem file43_85938 : ((((((p3 ∨ p0) ∧ (p7 → False)) ∧ ((False ∧ False) → False)) ∨ (((p6 → False) → False) → ((p0 → p5) → False))) ∧ ((((p4 ∧ p2) → False) → False) ∧ (((False ∧ p0) ∨ (p2 ∧ p1)) ∧ ((p7 → p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    apply False.elim assump_26
                case inr assump_25 =>
                  cases assump_25
                  case intro assump_30 assump_31 =>
                    have assump_107 : (p7 → p2) := by
                      intro assump_39
                      exact assump_30
                    let assump_38 := assump_23 assump_107
                    apply False.elim assump_38
          case inr assump_11 =>
            cases assump_3
            case intro assump_51 assump_52 =>
              cases assump_52
              case intro assump_55 assump_56 =>
                cases assump_55
                case inl assump_57 =>
                  cases assump_57
                  case intro assump_59 assump_60 =>
                    apply False.elim assump_59
                case inr assump_58 =>
                  cases assump_58
                  case intro assump_63 assump_64 =>
                    have assump_108 : (p7 → p2) := by
                      intro assump_72
                      exact assump_63
                    let assump_71 := assump_56 assump_108
                    apply False.elim assump_71
    case inr assump_5 =>
      cases assump_3
      case intro assump_80 assump_81 =>
        cases assump_81
        case intro assump_84 assump_85 =>
          cases assump_84
          case inl assump_86 =>
            cases assump_86
            case intro assump_88 assump_89 =>
              apply False.elim assump_88
          case inr assump_87 =>
            cases assump_87
            case intro assump_92 assump_93 =>
              have assump_109 : (p7 → p2) := by
                intro assump_101
                exact assump_92
              let assump_100 := assump_85 assump_109
              apply False.elim assump_100


variable (p4 p3 p1 p2 p5 : Prop)
theorem file43_88596 : ((((((p4 → p5) → (p1 ∧ p4)) → False) → (((p5 → True) ∨ (p1 → p3)) → ((False ∧ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p4 → p5) → (p1 ∧ p4)) → False) → (((p5 → True) ∨ (p1 → p3)) → ((False ∧ p2) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p0 p3 p5 p4 p1 p2 : Prop)
theorem file43_89118 : ((((((p5 ∨ p0) ∨ (p1 ∨ p6)) ∨ ((p3 ∨ p4) ∨ (p0 → False))) → False) ∧ ((((p4 ∨ p2) ∧ (p2 → False)) → ((p3 → False) → False)) ∨ (((p2 ∨ p2) ∨ (p2 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_38 : (((p5 ∨ p0) ∨ (p1 ∨ p6)) ∨ ((p3 ∨ p4) ∨ (p0 → False))) := by
        apply Or.inr
        apply Or.inr
        intro assump_12
        have assump_39 : (((p5 ∨ p0) ∨ (p1 ∨ p6)) ∨ ((p3 ∨ p4) ∨ (p0 → False))) := by
          apply Or.inl
          apply Or.inl
          apply Or.inr
          exact assump_12
        let assump_17 := assump_2 assump_39
        apply False.elim assump_17
      let assump_11 := assump_2 assump_38
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_40 : ((p2 ∨ p2) ∨ (p2 → False)) := by
        apply Or.inr
        intro assump_27
        have assump_41 : ((p2 ∨ p2) ∨ (p2 → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_27
        let assump_31 := assump_7 assump_41
        apply False.elim assump_31
      let assump_26 := assump_7 assump_40
      apply False.elim assump_26


variable (p3 p5 p7 p2 p4 p1 p6 : Prop)
theorem file43_90368 : (((((p5 → p1) ∨ (p1 ∧ p1)) ∧ ((p3 ∧ p7) ∧ (p3 → False))) → (((p6 → p3) → (p5 → True)) → ((p3 → False) ∧ (p2 → p7)))) ∨ ((((True → p6) → (p7 ∧ p4)) → ((p6 ∨ False) ∧ (p6 → False))) ∨ (((p6 → False) → False) → ((p3 → p2) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_9
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          have assump_85 : p3 := by
            exact assump_16
          let assump_24 := assump_15 assump_85
          apply False.elim assump_24
    case inr assump_11 =>
      cases assump_11
      case intro assump_28 assump_29 =>
        cases assump_9
        case intro assump_34 assump_35 =>
          cases assump_34
          case intro assump_36 assump_37 =>
            have assump_86 : p3 := by
              exact assump_36
            let assump_44 := assump_35 assump_86
            apply False.elim assump_44
  intro assump_48
  cases assump_1
  case intro assump_53 assump_54 =>
    cases assump_53
    case inl assump_55 =>
      cases assump_54
      case intro assump_59 assump_60 =>
        cases assump_59
        case intro assump_61 assump_62 =>
          exact assump_62
    case inr assump_56 =>
      cases assump_56
      case intro assump_69 assump_70 =>
        cases assump_54
        case intro assump_75 assump_76 =>
          cases assump_75
          case intro assump_77 assump_78 =>
            exact assump_78


variable (p7 p6 p0 p1 p4 p5 p3 : Prop)
theorem file43_92025 : (((((p1 ∧ p6) ∨ (False → False)) ∧ ((p7 → True) ∨ (p0 ∧ p4))) → False) → ((((True ∨ True) → False) → ((p0 → False) → (p0 ∨ p1))) → (((p1 ∨ p5) ∨ (p3 ∨ p5)) → ((p5 ∨ False) ∨ (p6 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      apply Or.inr
      intro assump_14
      have assump_55 : (((p1 ∧ p6) ∨ (False → False)) ∧ ((p7 → True) ∨ (p0 ∧ p4))) := by
        apply And.intro
        apply Or.inl
        apply And.intro
        exact assump_6
        exact assump_14
        apply Or.inl
        intro assump_19
        apply True.intro
      let assump_18 := assump_1 assump_55
      apply False.elim assump_18
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      exact assump_7
  case inr assump_5 =>
    cases assump_5
    case inl assump_29 =>
      apply Or.inr
      intro assump_37
      have assump_56 : (((p1 ∧ p6) ∨ (False → False)) ∧ ((p7 → True) ∨ (p0 ∧ p4))) := by
        apply And.intro
        apply Or.inr
        intro assump_42
        apply False.elim assump_42
        apply Or.inl
        intro assump_45
        apply True.intro
      let assump_41 := assump_1 assump_56
      apply False.elim assump_41
    case inr assump_30 =>
      apply Or.inl
      apply Or.inl
      exact assump_30


variable (p5 p7 p2 : Prop)
theorem file43_93416 : ((((((p5 ∧ p2) → (p7 ∨ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p5 ∧ p2) → (p7 ∨ True)) → False) → False) := by
    intro assump_5
    have assump_23 : ((p5 ∧ p2) → (p7 ∨ True)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p6 p2 p3 p0 p1 : Prop)
theorem file43_93970 : (((((p1 ∧ p0) → (p0 ∨ p4)) → False) ∧ (((p3 → False) ∧ (p0 ∧ p4)) ∧ ((p2 ∨ p6) → False))) → ((((p3 ∧ True) → (p2 → p0)) ∧ ((p3 ∧ p1) → False)) ∧ (((p3 ∧ p4) → (p1 → False)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_19
          case intro assump_22 assump_23 =>
            exact assump_22
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    cases assump_1
    case intro assump_37 assump_38 =>
      cases assump_38
      case intro assump_41 assump_42 =>
        cases assump_41
        case intro assump_43 assump_44 =>
          cases assump_44
          case intro assump_47 assump_48 =>
            have assump_98 : p3 := by
              exact assump_31
            let assump_58 := assump_43 assump_98
            apply False.elim assump_58
  intro assump_62
  cases assump_1
  case intro assump_65 assump_66 =>
    cases assump_66
    case intro assump_69 assump_70 =>
      cases assump_69
      case intro assump_71 assump_72 =>
        cases assump_72
        case intro assump_75 assump_76 =>
          have assump_99 : ((p1 ∧ p0) → (p0 ∨ p4)) := by
            intro assump_88
            cases assump_88
            case intro assump_89 assump_90 =>
              apply Or.inl
              exact assump_90
          let assump_87 := assump_65 assump_99
          apply False.elim assump_87


variable (p7 p0 p5 p2 p4 p3 p1 p6 : Prop)
theorem file43_95687 : (((((p4 → p2) → (p0 → p6)) ∧ ((p3 → False) → False)) ∧ (((True → False) → (p4 ∨ p6)) → False)) → ((((False ∨ p6) → False) → ((p1 ∨ p0) → False)) ∧ (((p6 ∧ p6) → False) ∧ ((p5 → p4) ∧ (p1 ∧ p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_146 : ((True → False) → (p4 ∨ p6)) := by
          intro assump_21
          have assump_147 : True := by
            apply True.intro
          let assump_24 := assump_21 assump_147
          apply False.elim assump_24
        let assump_20 := assump_11 assump_146
        apply False.elim assump_20
  case inr assump_5 =>
    cases assump_1
    case intro assump_35 assump_36 =>
      cases assump_35
      case intro assump_37 assump_38 =>
        have assump_148 : ((True → False) → (p4 ∨ p6)) := by
          intro assump_46
          have assump_149 : True := by
            apply True.intro
          let assump_49 := assump_46 assump_149
          apply False.elim assump_49
        let assump_45 := assump_36 assump_148
        apply False.elim assump_45
  apply And.intro
  intro assump_56
  cases assump_56
  case intro assump_57 assump_58 =>
    cases assump_1
    case intro assump_63 assump_64 =>
      cases assump_63
      case intro assump_65 assump_66 =>
        have assump_150 : ((True → False) → (p4 ∨ p6)) := by
          intro assump_74
          apply Or.inr
          exact assump_58
        let assump_73 := assump_64 assump_150
        apply False.elim assump_73
  apply And.intro
  intro assump_80
  cases assump_1
  case intro assump_83 assump_84 =>
    cases assump_83
    case intro assump_85 assump_86 =>
      have assump_151 : ((True → False) → (p4 ∨ p6)) := by
        intro assump_94
        have assump_152 : True := by
          apply True.intro
        let assump_97 := assump_94 assump_152
        apply False.elim assump_97
      let assump_93 := assump_84 assump_151
      apply False.elim assump_93
  apply And.intro
  cases assump_1
  case intro assump_104 assump_105 =>
    cases assump_104
    case intro assump_106 assump_107 =>
      have assump_153 : ((True → False) → (p4 ∨ p6)) := by
        intro assump_115
        have assump_154 : True := by
          apply True.intro
        let assump_118 := assump_115 assump_154
        apply False.elim assump_118
      let assump_114 := assump_105 assump_153
      apply False.elim assump_114
  cases assump_1
  case intro assump_125 assump_126 =>
    cases assump_125
    case intro assump_127 assump_128 =>
      have assump_155 : ((True → False) → (p4 ∨ p6)) := by
        intro assump_136
        have assump_156 : True := by
          apply True.intro
        let assump_139 := assump_136 assump_156
        apply False.elim assump_139
      let assump_135 := assump_126 assump_155
      apply False.elim assump_135


variable (p7 p0 p6 p1 p3 p5 : Prop)
theorem file43_98714 : (((((p6 → False) → (p3 → False)) ∧ ((p7 → p5) ∨ (p7 ∨ p0))) ∧ (((False ∧ p6) ∨ (p1 → p7)) ∨ ((p3 ∧ p5) → False))) → ((((p3 → p0) → False) → ((p7 → False) → (p7 → p7))) ∨ (((False ∧ p6) → False) → ((p5 ∧ False) → (p7 → p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
          case inr assump_15 =>
            apply Or.inl
            intro assump_22
            intro assump_23
            intro assump_24
            exact assump_24
        case inr assump_13 =>
          apply Or.inl
          intro assump_33
          intro assump_34
          intro assump_35
          exact assump_35
      case inr assump_9 =>
        cases assump_9
        case inl assump_42 =>
          cases assump_3
          case inl assump_46 =>
            cases assump_46
            case inl assump_48 =>
              cases assump_48
              case intro assump_50 assump_51 =>
                apply False.elim assump_50
            case inr assump_49 =>
              apply Or.inl
              intro assump_56
              intro assump_57
              intro assump_58
              exact assump_58
          case inr assump_47 =>
            apply Or.inl
            intro assump_67
            intro assump_68
            intro assump_69
            exact assump_69
        case inr assump_43 =>
          cases assump_3
          case inl assump_78 =>
            cases assump_78
            case inl assump_80 =>
              cases assump_80
              case intro assump_82 assump_83 =>
                apply False.elim assump_82
            case inr assump_81 =>
              apply Or.inl
              intro assump_88
              intro assump_89
              intro assump_90
              exact assump_90
          case inr assump_79 =>
            apply Or.inl
            intro assump_99
            intro assump_100
            intro assump_101
            exact assump_101


variable (p3 p2 p6 p0 p1 p4 p7 p5 : Prop)
theorem file43_101028 : (((((p2 ∨ False) ∧ (p3 ∨ p5)) ∧ ((True → False) ∨ (p4 → False))) ∨ (((p2 ∧ True) ∧ (True → p2)) → ((p6 ∨ p5) ∨ (p0 → p0)))) ∨ ((((p7 → False) → (p5 → p5)) → ((p6 → False) → False)) ∧ (((p2 ∨ False) → (p1 → False)) ∨ ((p3 → False) → (p1 → False))))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inr
      intro assump_12
      exact assump_12


variable (p7 p2 p6 p3 : Prop)
theorem file43_101553 : (((((False ∧ p6) → False) → False) → False) ∨ ((((p7 ∨ True) ∨ (p2 ∨ p3)) ∧ ((True → False) → (p3 ∧ p6))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((False ∧ p6) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p0 p1 p7 : Prop)
theorem file43_101977 : (((((p0 → False) → False) → ((p7 ∨ p1) ∨ (False → False))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p0 → False) → False) → ((p7 ∨ p1) ∨ (False → False))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p5 p3 p7 p2 p6 : Prop)
theorem file43_102369 : (((((True → False) → (True ∨ p7)) → ((False ∧ p7) ∧ (False ∨ p5))) → False) ∨ ((((p5 → False) ∨ (p1 → p3)) ∨ ((p1 ∨ p2) → (p6 → p5))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((True → False) → (True ∨ p7)) := by
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_13
  let assump_8 := And.left assump_4
  let assump_9 := And.left assump_8
  apply False.elim assump_9


variable (p6 p0 p1 p4 p3 p5 : Prop)
theorem file43_102861 : (((((p6 → False) ∨ (p6 ∧ p5)) → ((False ∧ p1) → False)) ∨ (((p0 ∨ p1) ∧ (p6 → p5)) ∨ ((p3 ∧ p4) ∧ (p3 ∨ p3)))) ∨ ((((p1 → p4) → False) ∧ ((p3 → p3) → False)) ∨ (((p0 → False) ∧ (p4 ∧ True)) → ((p3 → p0) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p1 p7 p0 p6 p4 p5 p3 p2 : Prop)
theorem file43_103293 : ((((((p6 ∨ p1) → (p6 → False)) ∧ ((p3 ∨ False) ∧ (p7 → p0))) → (((p5 → p6) ∧ (p0 → False)) ∨ ((p4 → p3) → (True → False)))) ∧ ((((p0 → False) → (p7 ∨ p2)) → ((True → p5) → (p5 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p0 → False) → (p7 ∨ p2)) → ((True → p5) → (p5 → True))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p5 p1 p7 : Prop)
theorem file43_103866 : (((((False ∧ p5) → False) → False) → False) ∨ ((((p7 → False) → (p1 ∧ p7)) → False) ∨ (((False → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((False ∧ p5) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p2 p6 p5 p3 p0 p1 p4 : Prop)
theorem file43_104313 : (((((False → False) ∧ (p3 → False)) → ((False ∨ False) ∨ (p3 ∨ False))) ∨ (((p2 → False) ∧ (p7 → p2)) ∨ ((p4 ∨ True) ∨ (p6 → p5)))) → ((((p5 ∧ False) ∧ (False ∧ True)) → ((p2 ∨ p2) → False)) ∨ (((p4 ∧ p2) → (p5 → p0)) → ((p1 ∧ True) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_6
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
    case inr assump_9 =>
      cases assump_6
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          apply False.elim assump_25
  case inr assump_3 =>
    cases assump_3
    case inl assump_30 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        apply Or.inl
        intro assump_38
        intro assump_39
        cases assump_39
        case inl assump_40 =>
          cases assump_38
          case intro assump_44 assump_45 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              apply False.elim assump_47
        case inr assump_41 =>
          cases assump_38
          case intro assump_54 assump_55 =>
            cases assump_54
            case intro assump_56 assump_57 =>
              apply False.elim assump_57
    case inr assump_31 =>
      cases assump_31
      case inl assump_62 =>
        cases assump_62
        case inl assump_64 =>
          apply Or.inl
          intro assump_68
          intro assump_69
          cases assump_69
          case inl assump_70 =>
            cases assump_68
            case intro assump_74 assump_75 =>
              cases assump_74
              case intro assump_76 assump_77 =>
                apply False.elim assump_77
          case inr assump_71 =>
            cases assump_68
            case intro assump_84 assump_85 =>
              cases assump_84
              case intro assump_86 assump_87 =>
                apply False.elim assump_87
        case inr assump_65 =>
          apply Or.inl
          intro assump_94
          intro assump_95
          cases assump_95
          case inl assump_96 =>
            cases assump_94
            case intro assump_100 assump_101 =>
              cases assump_100
              case intro assump_102 assump_103 =>
                apply False.elim assump_103
          case inr assump_97 =>
            cases assump_94
            case intro assump_110 assump_111 =>
              cases assump_110
              case intro assump_112 assump_113 =>
                apply False.elim assump_113
      case inr assump_63 =>
        apply Or.inl
        intro assump_120
        intro assump_121
        cases assump_121
        case inl assump_122 =>
          cases assump_120
          case intro assump_126 assump_127 =>
            cases assump_126
            case intro assump_128 assump_129 =>
              apply False.elim assump_129
        case inr assump_123 =>
          cases assump_120
          case intro assump_136 assump_137 =>
            cases assump_136
            case intro assump_138 assump_139 =>
              apply False.elim assump_139


variable (p6 p7 p2 p5 p3 p0 p4 : Prop)
theorem file43_107641 : (((((p4 → False) → False) ∧ ((p4 ∨ p6) → False)) → (((p6 → False) ∨ (p7 → p2)) → ((p2 → p5) ∧ (p3 ∧ p0)))) ∧ ((((p6 ∧ p5) → (p0 → p5)) → False) → (((True → p5) → (False ∨ p0)) → False))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      have assump_158 : (p4 → False) := by
        intro assump_18
        have assump_159 : (p4 ∨ p6) := by
          apply Or.inl
          exact assump_18
        let assump_22 := assump_11 assump_159
        apply False.elim assump_22
      let assump_17 := assump_10 assump_158
      apply False.elim assump_17
  case inr assump_7 =>
    cases assump_1
    case intro assump_31 assump_32 =>
      have assump_160 : (p4 → False) := by
        intro assump_39
        have assump_161 : (p4 ∨ p6) := by
          apply Or.inl
          exact assump_39
        let assump_43 := assump_32 assump_161
        apply False.elim assump_43
      let assump_38 := assump_31 assump_160
      apply False.elim assump_38
  apply And.intro
  cases assump_2
  case inl assump_50 =>
    cases assump_1
    case intro assump_54 assump_55 =>
      have assump_162 : (p4 → False) := by
        intro assump_62
        have assump_163 : (p4 ∨ p6) := by
          apply Or.inl
          exact assump_62
        let assump_66 := assump_55 assump_163
        apply False.elim assump_66
      let assump_61 := assump_54 assump_162
      apply False.elim assump_61
  case inr assump_51 =>
    cases assump_1
    case intro assump_75 assump_76 =>
      have assump_164 : (p4 → False) := by
        intro assump_83
        have assump_165 : (p4 ∨ p6) := by
          apply Or.inl
          exact assump_83
        let assump_87 := assump_76 assump_165
        apply False.elim assump_87
      let assump_82 := assump_75 assump_164
      apply False.elim assump_82
  cases assump_2
  case inl assump_94 =>
    cases assump_1
    case intro assump_98 assump_99 =>
      have assump_166 : (p4 → False) := by
        intro assump_106
        have assump_167 : (p4 ∨ p6) := by
          apply Or.inl
          exact assump_106
        let assump_110 := assump_99 assump_167
        apply False.elim assump_110
      let assump_105 := assump_98 assump_166
      apply False.elim assump_105
  case inr assump_95 =>
    cases assump_1
    case intro assump_119 assump_120 =>
      have assump_168 : (p4 → False) := by
        intro assump_127
        have assump_169 : (p4 ∨ p6) := by
          apply Or.inl
          exact assump_127
        let assump_131 := assump_120 assump_169
        apply False.elim assump_131
      let assump_126 := assump_119 assump_168
      apply False.elim assump_126
  intro assump_138
  intro assump_139
  have assump_170 : ((p6 ∧ p5) → (p0 → p5)) := by
    intro assump_145
    intro assump_146
    cases assump_145
    case intro assump_149 assump_150 =>
      exact assump_150
  let assump_144 := assump_138 assump_170
  apply False.elim assump_144


variable (p3 p0 p5 p1 p4 : Prop)
theorem file43_110729 : (((((p3 → p1) → (p3 → True)) ∨ ((p5 → p4) → False)) → False) → ((((p4 → False) → False) → ((False → False) ∧ (True ∧ p0))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_13 : (((p3 → p1) → (p3 → True)) ∨ ((p5 → p4) → False)) := by
    apply Or.inl
    intro assump_8
    intro assump_9
    apply True.intro
  let assump_7 := assump_1 assump_13
  apply False.elim assump_7


variable (p4 p6 p0 p7 : Prop)
theorem file43_111172 : (((((p7 → False) ∧ (p7 ∨ False)) ∧ ((p0 → False) ∨ (p7 ∨ p0))) ∧ (((p4 ∨ p0) ∨ (p6 ∧ p6)) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          cases assump_9
          case inl assump_18 =>
            have assump_54 : p7 := by
              exact assump_14
            let assump_27 := assump_10 assump_54
            apply False.elim assump_27
          case inr assump_19 =>
            cases assump_19
            case inl assump_31 =>
              have assump_55 : p7 := by
                exact assump_31
              let assump_40 := assump_10 assump_55
              apply False.elim assump_40
            case inr assump_32 =>
              have assump_56 : ((p4 ∨ p0) ∨ (p6 ∧ p6)) := by
                apply Or.inl
                apply Or.inr
                exact assump_32
              let assump_48 := assump_7 assump_56
              apply False.elim assump_48
        case inr assump_15 =>
          apply False.elim assump_15


variable (p7 p6 p0 p1 : Prop)
theorem file43_112393 : (((((p0 ∨ p6) → (p7 ∨ False)) → ((True → False) → False)) → (((True ∨ p7) ∨ (p1 → False)) → False)) → False) := by
  intro assump_19
  have assump_38 : (((p0 ∨ p6) → (p7 ∨ False)) → ((True → False) → False)) := by
    intro assump_23
    intro assump_24
    have assump_39 : True := by
      apply True.intro
    let assump_30 := assump_24 assump_39
    apply False.elim assump_30
  let assump_22 := assump_19 assump_38
  have assump_40 : ((True ∨ p7) ∨ (p1 → False)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_34 := assump_22 assump_40
  apply False.elim assump_34


variable (p2 p5 p4 p7 p0 : Prop)
theorem file43_113047 : ((((((p4 → False) ∨ (p5 → p7)) ∨ ((p2 ∨ p2) → False)) → (((False ∧ p4) ∧ (False ∨ False)) → ((p5 ∨ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p4 → False) ∨ (p5 → p7)) ∨ ((p2 ∨ p2) → False)) → (((False ∧ p4) ∧ (False ∨ False)) → ((p5 ∨ p0) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_6
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
    case inr assump_9 =>
      cases assump_6
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


