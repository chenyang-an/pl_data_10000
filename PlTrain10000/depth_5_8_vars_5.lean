variable (p2 p6 p4 p7 p5 p3 p1 : Prop)
theorem file5_47 : ((((((p5 ∨ True) ∨ (False → p1)) ∨ ((p4 → p1) → False)) → False) ∨ ((((False ∧ False) ∧ (p3 ∨ p7)) ∧ ((False ∨ p6) → (p1 ∨ p3))) ∧ (((p3 → p2) → False) → ((p1 → False) ∧ (p1 ∧ p1))))) → False) := by
  intro assump_16
  cases assump_16
  case inl assump_17 =>
    have assump_35 : (((p5 ∨ True) ∨ (False → p1)) ∨ ((p4 → p1) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_21 := assump_17 assump_35
    apply False.elim assump_21
  case inr assump_18 =>
    cases assump_18
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            apply False.elim assump_31


variable (p3 p5 p7 p4 p0 p2 p6 : Prop)
theorem file5_920 : (((((p3 ∨ p7) → (p5 → p7)) → ((False → False) ∧ (True → True))) ∨ (((p2 → False) → False) → False)) ∨ ((((p2 ∧ p5) → False) ∧ ((False ∨ p0) → False)) ∧ (((p4 → False) ∨ (p6 → p4)) ∨ ((p0 ∧ p5) ∧ (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  apply True.intro


variable (p5 p7 p6 p1 p4 p2 : Prop)
theorem file5_1344 : (((((p5 ∨ p1) ∧ (p5 → False)) ∨ ((True → False) → (p2 → p7))) ∨ (((False → p7) ∨ (p2 ∨ p6)) → False)) → ((((p4 → p2) → (p5 → False)) → ((p1 ∨ True) ∨ (p4 → p4))) ∨ (((p5 ∨ p6) ∨ (False ∨ p6)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inl
          intro assump_14
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_9 =>
          apply Or.inl
          intro assump_21
          apply Or.inl
          apply Or.inl
          exact assump_9
    case inr assump_5 =>
      apply Or.inl
      intro assump_26
      apply Or.inl
      apply Or.inr
      apply True.intro
  case inr assump_3 =>
    apply Or.inl
    intro assump_31
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p4 p3 p2 p1 p6 : Prop)
theorem file5_2335 : (((((False ∧ True) ∨ (p6 → False)) → False) ∧ (((p1 ∨ p6) ∧ (p6 ∨ p3)) → False)) → ((((p2 ∧ p4) ∨ (p1 ∧ False)) → ((True ∧ True) ∧ (p3 ∧ p1))) ∨ (((p2 ∨ p2) ∧ (True → p6)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    apply And.intro
    apply And.intro
    apply True.intro
    apply True.intro
    apply And.intro
    cases assump_8
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_71 : ((False ∧ True) ∨ (p6 → False)) := by
          apply Or.inr
          intro assump_21
          have assump_72 : ((p1 ∨ p6) ∧ (p6 ∨ p3)) := by
            apply And.intro
            apply Or.inr
            exact assump_21
            apply Or.inl
            exact assump_21
          let assump_27 := assump_3 assump_72
          apply False.elim assump_27
        let assump_20 := assump_2 assump_71
        apply False.elim assump_20
    case inr assump_10 =>
      cases assump_10
      case intro assump_34 assump_35 =>
        apply False.elim assump_35
    cases assump_8
    case inl assump_40 =>
      cases assump_40
      case intro assump_42 assump_43 =>
        have assump_73 : ((False ∧ True) ∨ (p6 → False)) := by
          apply Or.inr
          intro assump_52
          have assump_74 : ((p1 ∨ p6) ∧ (p6 ∨ p3)) := by
            apply And.intro
            apply Or.inr
            exact assump_52
            apply Or.inl
            exact assump_52
          let assump_58 := assump_3 assump_74
          apply False.elim assump_58
        let assump_51 := assump_2 assump_73
        apply False.elim assump_51
    case inr assump_41 =>
      cases assump_41
      case intro assump_65 assump_66 =>
        apply False.elim assump_66


variable (p2 p4 p1 p5 p7 : Prop)
theorem file5_4175 : ((((((True → False) → (p2 → False)) → False) → (((p7 → True) ∨ (p7 ∨ p5)) ∨ ((p1 → False) → (p4 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((True → False) → (p2 → False)) → False) → (((p7 → True) ∨ (p7 ∨ p5)) ∨ ((p1 → False) → (p4 ∨ True)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p6 p7 p3 : Prop)
theorem file5_4665 : (((((p6 ∨ p3) → False) → False) ∧ (((False → p6) ∨ (p7 → p4)) → ((False → p3) ∧ (False ∧ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : ((False → p6) ∨ (p7 → p4)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_18
    let assump_12 := And.right assump_8
    let assump_14 := And.left assump_12
    apply False.elim assump_14


variable (p5 p2 p1 p7 p0 p3 p6 p4 : Prop)
theorem file5_5189 : (((((p5 → p6) → (p7 ∨ True)) ∨ ((p0 ∧ True) ∧ (p7 → p3))) ∨ (((p5 ∨ p4) ∨ (p6 ∧ p5)) ∧ ((p5 → False) → (p1 → p3)))) ∨ ((((p2 → p7) ∨ (True → False)) ∧ ((True ∧ p4) → (True → False))) → (((p4 → False) → (p5 ∧ True)) ∨ ((True ∨ p3) → (False → p5))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply True.intro


variable (p7 p2 p3 p1 p6 p5 p0 : Prop)
theorem file5_5603 : (((((p5 ∨ p7) → (p0 ∨ p7)) → ((False ∨ p6) → False)) ∧ (((p7 → False) ∨ (p7 → False)) ∨ ((p7 ∧ p3) → False))) → ((((True → p2) → False) ∨ ((p0 → p2) → False)) → (((True → False) → (p1 → False)) ∨ ((p6 ∧ p0) ∧ (p5 ∨ True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          intro assump_17
          intro assump_18
          have assump_97 : True := by
            apply True.intro
          let assump_23 := assump_17 assump_97
          apply False.elim assump_23
        case inr assump_14 =>
          apply Or.inl
          intro assump_29
          intro assump_30
          have assump_98 : True := by
            apply True.intro
          let assump_35 := assump_29 assump_98
          apply False.elim assump_35
      case inr assump_12 =>
        apply Or.inl
        intro assump_41
        intro assump_42
        have assump_99 : True := by
          apply True.intro
        let assump_47 := assump_41 assump_99
        apply False.elim assump_47
  case inr assump_4 =>
    cases assump_1
    case intro assump_53 assump_54 =>
      cases assump_54
      case inl assump_57 =>
        cases assump_57
        case inl assump_59 =>
          apply Or.inl
          intro assump_63
          intro assump_64
          have assump_100 : True := by
            apply True.intro
          let assump_69 := assump_63 assump_100
          apply False.elim assump_69
        case inr assump_60 =>
          apply Or.inl
          intro assump_75
          intro assump_76
          have assump_101 : True := by
            apply True.intro
          let assump_81 := assump_75 assump_101
          apply False.elim assump_81
      case inr assump_58 =>
        apply Or.inl
        intro assump_87
        intro assump_88
        have assump_102 : True := by
          apply True.intro
        let assump_93 := assump_87 assump_102
        apply False.elim assump_93


variable (p0 p7 p4 p1 : Prop)
theorem file5_7754 : ((((((p1 ∨ p1) ∨ (p0 ∧ p0)) → ((False ∨ p7) → False)) → (((p4 ∨ True) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p1 ∨ p1) ∨ (p0 ∧ p0)) → ((False ∨ p7) → False)) → (((p4 ∨ True) → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_20 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_12 := assump_6 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p2 p6 p4 p7 p3 : Prop)
theorem file5_8311 : ((((((p5 → False) → False) → ((True → p6) → (p6 → False))) → (((p6 ∧ p2) → False) ∨ ((p2 → p4) ∨ (False → p5)))) ∧ ((((p2 → True) ∨ (p5 ∧ p7)) ∨ ((p7 ∧ p6) ∧ (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (((p2 → True) ∨ (p5 ∧ p7)) ∨ ((p7 ∧ p6) ∧ (p3 → False))) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p0 p1 p6 p2 p5 : Prop)
theorem file5_8869 : (((((p0 → False) ∧ (True ∧ p5)) → False) ∧ (((p2 ∨ False) ∧ (p6 ∨ False)) ∧ ((p5 ∨ p5) ∧ (p2 → False)))) → ((((p2 → False) ∨ (p1 ∧ p0)) ∧ ((False ∧ False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case inl assump_19 =>
              cases assump_18
              case inl assump_23 =>
                cases assump_16
                case intro assump_27 assump_28 =>
                  cases assump_27
                  case inl assump_29 =>
                    have assump_99 : p2 := by
                      exact assump_19
                    let assump_35 := assump_28 assump_99
                    apply False.elim assump_35
                  case inr assump_30 =>
                    have assump_100 : p2 := by
                      exact assump_19
                    let assump_43 := assump_28 assump_100
                    apply False.elim assump_43
              case inr assump_24 =>
                apply False.elim assump_24
            case inr assump_20 =>
              apply False.elim assump_20
    case inr assump_6 =>
      cases assump_6
      case intro assump_51 assump_52 =>
        cases assump_1
        case intro assump_59 assump_60 =>
          cases assump_60
          case intro assump_63 assump_64 =>
            cases assump_63
            case intro assump_65 assump_66 =>
              cases assump_65
              case inl assump_67 =>
                cases assump_66
                case inl assump_71 =>
                  cases assump_64
                  case intro assump_75 assump_76 =>
                    cases assump_75
                    case inl assump_77 =>
                      have assump_101 : p2 := by
                        exact assump_67
                      let assump_83 := assump_76 assump_101
                      apply False.elim assump_83
                    case inr assump_78 =>
                      have assump_102 : p2 := by
                        exact assump_67
                      let assump_91 := assump_76 assump_102
                      apply False.elim assump_91
                case inr assump_72 =>
                  apply False.elim assump_72
              case inr assump_68 =>
                apply False.elim assump_68


variable (p1 p2 p7 p0 p5 p6 p3 : Prop)
theorem file5_11490 : (((((p5 → False) ∨ (p3 → False)) ∧ ((p1 ∧ p5) ∨ (p7 → False))) ∧ (((p7 ∧ p0) ∧ (p6 → p0)) ∧ ((p2 → p2) → False))) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case intro assump_21 assump_22 =>
      cases assump_21
      case inl assump_23 =>
        cases assump_22
        case inl assump_27 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            cases assump_20
            case intro assump_35 assump_36 =>
              cases assump_35
              case intro assump_37 assump_38 =>
                cases assump_37
                case intro assump_39 assump_40 =>
                  have assump_133 : (p2 → p2) := by
                    intro assump_50
                    exact assump_50
                  let assump_49 := assump_36 assump_133
                  apply False.elim assump_49
        case inr assump_28 =>
          cases assump_20
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              cases assump_60
              case intro assump_62 assump_63 =>
                have assump_134 : (p2 → p2) := by
                  intro assump_73
                  exact assump_73
                let assump_72 := assump_59 assump_134
                apply False.elim assump_72
      case inr assump_24 =>
        cases assump_22
        case inl assump_81 =>
          cases assump_81
          case intro assump_83 assump_84 =>
            cases assump_20
            case intro assump_89 assump_90 =>
              cases assump_89
              case intro assump_91 assump_92 =>
                cases assump_91
                case intro assump_93 assump_94 =>
                  have assump_135 : (p2 → p2) := by
                    intro assump_104
                    exact assump_104
                  let assump_103 := assump_90 assump_135
                  apply False.elim assump_103
        case inr assump_82 =>
          cases assump_20
          case intro assump_112 assump_113 =>
            cases assump_112
            case intro assump_114 assump_115 =>
              cases assump_114
              case intro assump_116 assump_117 =>
                have assump_136 : (p2 → p2) := by
                  intro assump_127
                  exact assump_127
                let assump_126 := assump_113 assump_136
                apply False.elim assump_126


variable (p5 p7 p1 p6 p3 p0 p2 p4 : Prop)
theorem file5_14010 : ((((((p0 ∨ p6) → False) ∨ ((p7 → p6) ∨ (p5 → p3))) → (((p1 ∨ p4) ∧ (p0 → p4)) → ((p5 → False) ∧ (p0 ∨ p2)))) ∧ ((((False → p2) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → p2) → False) → False) := by
      intro assump_9
      have assump_23 : (False → p2) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p2 p5 p6 p4 p3 p7 p0 : Prop)
theorem file5_14637 : (((((p2 ∧ p5) → False) ∨ ((p2 → p6) → False)) ∨ (((p7 → False) ∧ (p4 → False)) → False)) → ((((p3 ∧ p3) → (False → False)) ∨ ((False → False) ∨ (p0 → False))) ∨ (((p6 ∧ p3) → False) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply Or.inl
      intro assump_8
      intro assump_9
      apply False.elim assump_9
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_14
      intro assump_15
      apply False.elim assump_15
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_20
    intro assump_21
    apply False.elim assump_21


variable (p0 p7 p3 p2 p6 p4 p1 : Prop)
theorem file5_15380 : (((((p1 ∧ p6) ∨ (p7 → False)) → False) → False) → ((((p3 ∨ p0) ∨ (p0 → p1)) ∧ ((False → p2) ∧ (p3 ∨ False))) → (((p3 ∨ False) → False) → ((p0 → True) ∨ (p4 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_15
          case inl assump_18 =>
            apply Or.inl
            intro assump_24
            apply True.intro
          case inr assump_19 =>
            apply False.elim assump_19
      case inr assump_11 =>
        cases assump_7
        case intro assump_29 assump_30 =>
          cases assump_30
          case inl assump_33 =>
            apply Or.inl
            intro assump_39
            apply True.intro
          case inr assump_34 =>
            apply False.elim assump_34
    case inr assump_9 =>
      cases assump_7
      case intro assump_44 assump_45 =>
        cases assump_45
        case inl assump_48 =>
          apply Or.inl
          intro assump_54
          apply True.intro
        case inr assump_49 =>
          apply False.elim assump_49


variable (p1 p0 p3 p2 p4 p6 : Prop)
theorem file5_16673 : (((((p0 → False) → (p6 ∨ True)) → ((p1 → False) → False)) → (((p6 ∨ p3) ∨ (p4 ∨ p2)) → ((p6 ∧ p0) ∧ (False → p0)))) → ((((p2 ∧ False) → False) ∨ ((p3 ∧ p6) → (p3 ∧ p2))) ∨ (((p4 → p6) → (p1 ∨ p4)) ∨ ((p3 ∨ p6) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p1 p6 p5 p3 : Prop)
theorem file5_17100 : ((((((p5 → p5) ∨ (False ∨ p5)) → False) → (((p3 → False) ∨ (False ∧ p1)) → ((True → False) ∨ (p5 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p5 → p5) ∨ (False ∨ p5)) → False) → (((p3 → False) ∨ (False ∧ p1)) → ((True → False) ∨ (p5 ∧ p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      intro assump_13
      have assump_31 : ((p5 → p5) ∨ (False ∨ p5)) := by
        apply Or.inl
        intro assump_17
        exact assump_17
      let assump_16 := assump_5 assump_31
      apply False.elim assump_16
    case inr assump_8 =>
      cases assump_8
      case intro assump_23 assump_24 =>
        apply False.elim assump_23
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p7 p6 p5 p3 p4 p1 : Prop)
theorem file5_17945 : ((((((p4 → False) ∧ (True ∧ False)) → ((p4 → False) ∨ (p7 → False))) → False) ∧ ((((True ∨ p6) ∧ (p6 ∨ p1)) ∧ ((p3 ∧ p3) → False)) → (((p6 → False) ∧ (p6 → True)) ∨ ((p5 → p1) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p4 → False) ∧ (True ∧ False)) → ((p4 → False) ∨ (p7 → False))) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
    let assump_9 := assump_2 assump_24
    apply False.elim assump_9


variable (p6 p5 p7 p4 p2 p0 p1 p3 : Prop)
theorem file5_18631 : ((((((p6 ∧ p4) → False) → ((p4 ∧ True) → (True → False))) ∨ (((p0 ∨ p2) ∨ (p2 ∨ True)) → ((p2 → False) → (p2 → False)))) ∧ ((((p6 ∨ p6) ∧ (p7 → p3)) → ((True ∨ p6) ∨ (p1 ∨ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_48 : (((p6 ∨ p6) ∧ (p7 → p3)) → ((True ∨ p6) ∨ (p1 ∨ p5))) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_15 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
      let assump_10 := assump_3 assump_48
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_49 : (((p6 ∨ p6) ∧ (p7 → p3)) → ((True ∨ p6) ∨ (p1 ∨ p5))) := by
        intro assump_32
        cases assump_32
        case intro assump_33 assump_34 =>
          cases assump_33
          case inl assump_35 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_36 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
      let assump_31 := assump_3 assump_49
      apply False.elim assump_31


variable (p0 p6 p7 p3 p1 p5 p4 : Prop)
theorem file5_20026 : (((((True → False) ∧ (True → p3)) → ((p5 ∨ p7) → (p6 ∨ p5))) ∨ (((p4 ∨ p4) → (p5 → p4)) ∨ ((p4 → True) → False))) ∨ ((((p5 ∨ p5) → (p1 → False)) ∨ ((p3 → False) → (p3 ∨ p0))) ∨ (((p5 ∨ p6) ∧ (False ∧ p0)) ∨ ((p6 ∧ p4) ∨ (p5 ∧ p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      apply Or.inr
      exact assump_3
  case inr assump_4 =>
    cases assump_1
    case intro assump_15 assump_16 =>
      have assump_27 : True := by
        apply True.intro
      let assump_23 := assump_15 assump_27
      apply False.elim assump_23


variable (p2 p3 p5 p6 p4 p7 p0 : Prop)
theorem file5_20743 : (((((p4 ∧ p0) → (p7 ∨ p6)) ∧ ((False → p0) → (p2 ∧ False))) → False) ∨ ((((p3 → p2) → False) → False) ∧ (((p3 ∧ p5) → (p0 → False)) → ((p6 ∧ p7) ∧ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (False → p0) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_17
    let assump_12 := And.right assump_8
    apply False.elim assump_12


variable (p7 p6 p1 p0 p2 : Prop)
theorem file5_21256 : ((((((False → False) ∧ (True → False)) → False) ∨ (((p2 → False) → (p6 → p1)) ∧ ((p7 ∧ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False → False) ∧ (True → False)) → False) ∨ (((p2 → False) → (p6 → p1)) ∧ ((p7 ∧ p0) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p6 p5 p7 p0 p3 p2 p4 : Prop)
theorem file5_21880 : (((((p4 → False) → (p5 ∨ False)) → ((p1 → False) ∨ (True ∨ False))) → (((p0 ∨ True) ∨ (p1 ∧ p4)) ∨ ((p2 → p1) → (True → p3)))) ∨ ((((p3 → p3) ∧ (p7 → False)) ∧ ((True ∨ p3) → False)) → (((False → False) → (p7 ∨ p6)) ∧ ((True → False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p4 p7 p2 p1 p5 p3 p0 : Prop)
theorem file5_22291 : ((((((p7 ∨ p7) ∨ (p4 → False)) ∧ ((p1 ∨ p4) ∧ (p5 → p4))) ∧ (((p7 → False) → (True ∨ p4)) ∧ ((p7 ∧ True) → (p0 → p7)))) ∧ ((((p1 ∨ False) ∨ (p4 → p2)) → False) ∧ (((p4 → True) ∨ (p7 ∧ p3)) → False))) → False) := by
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
            case intro assump_14 assump_15 =>
              cases assump_14
              case inl assump_16 =>
                cases assump_5
                case intro assump_22 assump_23 =>
                  cases assump_3
                  case intro assump_28 assump_29 =>
                    have assump_156 : ((p4 → True) ∨ (p7 ∧ p3)) := by
                      apply Or.inl
                      intro assump_35
                      apply True.intro
                    let assump_34 := assump_29 assump_156
                    apply False.elim assump_34
              case inr assump_17 =>
                cases assump_5
                case intro assump_43 assump_44 =>
                  cases assump_3
                  case intro assump_49 assump_50 =>
                    have assump_157 : ((p4 → True) ∨ (p7 ∧ p3)) := by
                      apply Or.inl
                      intro assump_56
                      apply True.intro
                    let assump_55 := assump_50 assump_157
                    apply False.elim assump_55
          case inr assump_11 =>
            cases assump_7
            case intro assump_62 assump_63 =>
              cases assump_62
              case inl assump_64 =>
                cases assump_5
                case intro assump_70 assump_71 =>
                  cases assump_3
                  case intro assump_76 assump_77 =>
                    have assump_158 : ((p4 → True) ∨ (p7 ∧ p3)) := by
                      apply Or.inl
                      intro assump_83
                      apply True.intro
                    let assump_82 := assump_77 assump_158
                    apply False.elim assump_82
              case inr assump_65 =>
                cases assump_5
                case intro assump_91 assump_92 =>
                  cases assump_3
                  case intro assump_97 assump_98 =>
                    have assump_159 : ((p4 → True) ∨ (p7 ∧ p3)) := by
                      apply Or.inl
                      intro assump_104
                      apply True.intro
                    let assump_103 := assump_98 assump_159
                    apply False.elim assump_103
        case inr assump_9 =>
          cases assump_7
          case intro assump_110 assump_111 =>
            cases assump_110
            case inl assump_112 =>
              cases assump_5
              case intro assump_118 assump_119 =>
                cases assump_3
                case intro assump_124 assump_125 =>
                  have assump_160 : ((p4 → True) ∨ (p7 ∧ p3)) := by
                    apply Or.inl
                    intro assump_131
                    apply True.intro
                  let assump_130 := assump_125 assump_160
                  apply False.elim assump_130
            case inr assump_113 =>
              cases assump_5
              case intro assump_139 assump_140 =>
                cases assump_3
                case intro assump_145 assump_146 =>
                  have assump_161 : ((p4 → True) ∨ (p7 ∧ p3)) := by
                    apply Or.inl
                    intro assump_152
                    apply True.intro
                  let assump_151 := assump_146 assump_161
                  apply False.elim assump_151


variable (p3 p5 p4 p0 p6 : Prop)
theorem file5_26132 : (((((p6 → p6) ∧ (p0 → p0)) ∧ ((p6 → p6) → False)) → False) ∨ ((((p0 ∨ p3) → False) ∨ ((True ∧ p4) ∨ (p3 → p0))) ∧ (((p4 ∨ p3) ∨ (p4 → p3)) → ((p0 ∧ False) → (p5 ∧ p6))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_19 : (p6 → p6) := by
        intro assump_13
        exact assump_13
      let assump_12 := assump_3 assump_19
      apply False.elim assump_12


variable (p1 p5 p7 p0 p2 : Prop)
theorem file5_26666 : ((((((p5 ∧ p0) → (False ∨ p5)) ∨ ((False ∧ p0) ∨ (p1 ∧ p2))) ∨ (((p2 ∨ p7) → False) → False)) → False) → False) := by
  intro assump_41
  have assump_55 : ((((p5 ∧ p0) → (False ∨ p5)) ∨ ((False ∧ p0) ∨ (p1 ∧ p2))) ∨ (((p2 ∨ p7) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_45
    cases assump_45
    case intro assump_46 assump_47 =>
      apply Or.inr
      exact assump_46
  let assump_44 := assump_41 assump_55
  apply False.elim assump_44


variable (p1 p6 p0 p7 p3 p4 : Prop)
theorem file5_27200 : (((((p0 ∨ p1) ∧ (False ∧ p7)) → False) → False) → ((((p3 → False) → False) → ((p0 ∧ False) → False)) ∨ (((p6 ∨ False) ∧ (p1 → False)) → ((p4 → False) ∨ (True ∨ True))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p3 p6 : Prop)
theorem file5_27571 : (((((True ∨ p3) → False) → ((p6 ∨ False) ∧ (True ∨ p6))) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((True → False) → False) := by
      intro assump_9
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p0 p4 p7 p3 p2 p1 p5 : Prop)
theorem file5_28088 : (((((p1 ∧ p0) → (p4 ∨ p1)) ∨ ((False ∨ p2) ∧ (True ∧ p0))) → False) → ((((p7 → False) → False) → False) ∧ (((p0 → False) ∧ (p1 → p3)) ∧ ((False ∧ p1) ∧ (p2 ∨ p5))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_89 : (((p1 ∧ p0) → (p4 ∨ p1)) ∨ ((False ∨ p2) ∧ (True ∧ p0))) := by
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply Or.inr
      exact assump_9
  let assump_7 := assump_1 assump_89
  apply False.elim assump_7
  apply And.intro
  apply And.intro
  intro assump_18
  have assump_90 : (((p1 ∧ p0) → (p4 ∨ p1)) ∨ ((False ∨ p2) ∧ (True ∧ p0))) := by
    apply Or.inl
    intro assump_24
    cases assump_24
    case intro assump_25 assump_26 =>
      apply Or.inr
      exact assump_25
  let assump_23 := assump_1 assump_90
  apply False.elim assump_23
  intro assump_34
  have assump_91 : (((p1 ∧ p0) → (p4 ∨ p1)) ∨ ((False ∨ p2) ∧ (True ∧ p0))) := by
    apply Or.inl
    intro assump_40
    cases assump_40
    case intro assump_41 assump_42 =>
      apply Or.inr
      exact assump_41
  let assump_39 := assump_1 assump_91
  apply False.elim assump_39
  apply And.intro
  apply And.intro
  have assump_92 : (((p1 ∧ p0) → (p4 ∨ p1)) ∨ ((False ∨ p2) ∧ (True ∧ p0))) := by
    apply Or.inl
    intro assump_53
    cases assump_53
    case intro assump_54 assump_55 =>
      apply Or.inr
      exact assump_54
  let assump_52 := assump_1 assump_92
  apply False.elim assump_52
  have assump_93 : (((p1 ∧ p0) → (p4 ∨ p1)) ∨ ((False ∨ p2) ∧ (True ∧ p0))) := by
    apply Or.inl
    intro assump_66
    cases assump_66
    case intro assump_67 assump_68 =>
      apply Or.inr
      exact assump_67
  let assump_65 := assump_1 assump_93
  apply False.elim assump_65
  have assump_94 : (((p1 ∧ p0) → (p4 ∨ p1)) ∨ ((False ∨ p2) ∧ (True ∧ p0))) := by
    apply Or.inl
    intro assump_79
    cases assump_79
    case intro assump_80 assump_81 =>
      apply Or.inr
      exact assump_80
  let assump_78 := assump_1 assump_94
  apply False.elim assump_78


variable (p2 p3 p1 p6 p4 p7 p5 : Prop)
theorem file5_30187 : (((((True ∨ p3) ∧ (p2 → False)) → False) ∧ (((p2 ∨ p1) ∨ (p4 ∧ True)) → ((p5 → p3) → (p6 ∧ p7)))) → ((((p3 ∨ True) ∨ (p5 ∧ True)) → ((False ∧ p7) ∨ (False → p2))) ∧ (((p5 ∧ False) → False) ∨ ((p3 → False) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        apply Or.inr
        intro assump_15
        apply False.elim assump_15
    case inr assump_6 =>
      cases assump_1
      case intro assump_20 assump_21 =>
        apply Or.inr
        intro assump_26
        apply False.elim assump_26
  case inr assump_4 =>
    cases assump_4
    case intro assump_29 assump_30 =>
      cases assump_1
      case intro assump_35 assump_36 =>
        apply Or.inr
        intro assump_41
        apply False.elim assump_41
  cases assump_1
  case intro assump_44 assump_45 =>
    apply Or.inl
    intro assump_50
    cases assump_50
    case intro assump_51 assump_52 =>
      apply False.elim assump_52


variable (p7 p5 p3 p6 p4 p2 p1 p0 : Prop)
theorem file5_31320 : (((((p6 ∨ p2) → False) → ((p1 ∨ p4) → (p6 → False))) ∨ (((p6 ∧ p1) → (p7 → p5)) ∨ ((True → p3) ∧ (p2 → p0)))) ∨ ((((p7 ∧ p2) → (p3 → p1)) ∧ ((p6 ∧ p7) ∨ (p2 → False))) ∧ (((p1 → False) ∧ (p0 ∧ p0)) ∧ ((p6 → False) → (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    have assump_24 : (p6 ∨ p2) := by
      apply Or.inl
      exact assump_3
    let assump_12 := assump_1 assump_24
    apply False.elim assump_12
  case inr assump_7 =>
    have assump_25 : (p6 ∨ p2) := by
      apply Or.inl
      exact assump_3
    let assump_20 := assump_1 assump_25
    apply False.elim assump_20


variable (p4 p6 p0 p1 p3 p2 : Prop)
theorem file5_32059 : (((((p0 → False) → (p3 → True)) → False) ∧ (((p1 ∨ p0) ∨ (p6 ∨ p1)) ∧ ((p1 → False) ∨ (p2 ∨ p4)))) → False) := by
  intro assump_101
  cases assump_101
  case intro assump_102 assump_103 =>
    cases assump_103
    case intro assump_106 assump_107 =>
      cases assump_106
      case inl assump_108 =>
        cases assump_108
        case inl assump_110 =>
          cases assump_107
          case inl assump_114 =>
            have assump_250 : p1 := by
              exact assump_110
            let assump_118 := assump_114 assump_250
            apply False.elim assump_118
          case inr assump_115 =>
            cases assump_115
            case inl assump_122 =>
              have assump_251 : ((p0 → False) → (p3 → True)) := by
                intro assump_129
                intro assump_130
                apply True.intro
              let assump_128 := assump_102 assump_251
              apply False.elim assump_128
            case inr assump_123 =>
              have assump_252 : ((p0 → False) → (p3 → True)) := by
                intro assump_139
                intro assump_140
                apply True.intro
              let assump_138 := assump_102 assump_252
              apply False.elim assump_138
        case inr assump_111 =>
          cases assump_107
          case inl assump_146 =>
            have assump_253 : ((p0 → False) → (p3 → True)) := by
              intro assump_153
              intro assump_154
              apply True.intro
            let assump_152 := assump_102 assump_253
            apply False.elim assump_152
          case inr assump_147 =>
            cases assump_147
            case inl assump_158 =>
              have assump_254 : ((p0 → False) → (p3 → True)) := by
                intro assump_165
                intro assump_166
                apply True.intro
              let assump_164 := assump_102 assump_254
              apply False.elim assump_164
            case inr assump_159 =>
              have assump_255 : ((p0 → False) → (p3 → True)) := by
                intro assump_175
                intro assump_176
                apply True.intro
              let assump_174 := assump_102 assump_255
              apply False.elim assump_174
      case inr assump_109 =>
        cases assump_109
        case inl assump_180 =>
          cases assump_107
          case inl assump_184 =>
            have assump_256 : ((p0 → False) → (p3 → True)) := by
              intro assump_191
              intro assump_192
              apply True.intro
            let assump_190 := assump_102 assump_256
            apply False.elim assump_190
          case inr assump_185 =>
            cases assump_185
            case inl assump_196 =>
              have assump_257 : ((p0 → False) → (p3 → True)) := by
                intro assump_203
                intro assump_204
                apply True.intro
              let assump_202 := assump_102 assump_257
              apply False.elim assump_202
            case inr assump_197 =>
              have assump_258 : ((p0 → False) → (p3 → True)) := by
                intro assump_213
                intro assump_214
                apply True.intro
              let assump_212 := assump_102 assump_258
              apply False.elim assump_212
        case inr assump_181 =>
          cases assump_107
          case inl assump_220 =>
            have assump_259 : p1 := by
              exact assump_181
            let assump_224 := assump_220 assump_259
            apply False.elim assump_224
          case inr assump_221 =>
            cases assump_221
            case inl assump_228 =>
              have assump_260 : ((p0 → False) → (p3 → True)) := by
                intro assump_235
                intro assump_236
                apply True.intro
              let assump_234 := assump_102 assump_260
              apply False.elim assump_234
            case inr assump_229 =>
              have assump_261 : ((p0 → False) → (p3 → True)) := by
                intro assump_245
                intro assump_246
                apply True.intro
              let assump_244 := assump_102 assump_261
              apply False.elim assump_244


variable (p7 p1 p5 p0 p3 : Prop)
theorem file5_36310 : (((((p7 ∧ p3) ∨ (p3 ∨ p1)) → False) ∧ (((p5 ∧ False) → (p0 ∨ p3)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p5 ∧ False) → (p0 ∨ p3)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p6 p2 p3 p5 p1 : Prop)
theorem file5_36766 : ((((((p3 ∨ p1) → False) ∨ ((p5 ∧ True) → (p3 ∨ p2))) → (((p6 → p6) → False) → ((p3 → False) → (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_36 : ((((p3 ∨ p1) → False) ∨ ((p5 ∧ True) → (p3 ∨ p2))) → (((p6 → p6) → False) → ((p3 → False) → (p3 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_5
    case inl assump_15 =>
      have assump_37 : (p3 ∨ p1) := by
        apply Or.inl
        exact assump_8
      let assump_19 := assump_15 assump_37
      apply False.elim assump_19
    case inr assump_16 =>
      have assump_38 : (p6 → p6) := by
        intro assump_27
        exact assump_27
      let assump_26 := assump_6 assump_38
      apply False.elim assump_26
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p2 p3 p4 p5 p6 p7 : Prop)
theorem file5_37643 : ((((((False ∧ p7) ∨ (False → True)) ∧ ((p7 ∨ p4) ∧ (p3 → False))) ∨ (((False ∨ p5) ∨ (False → False)) ∨ ((p6 ∨ p6) → (p2 ∨ p6)))) → False) → False) := by
  intro assump_5
  have assump_16 : ((((False ∧ p7) ∨ (False → True)) ∧ ((p7 ∨ p4) ∧ (p3 → False))) ∨ (((False ∨ p5) ∨ (False → False)) ∨ ((p6 ∨ p6) → (p2 ∨ p6)))) := by
    apply Or.inr
    apply Or.inl
    apply Or.inr
    intro assump_10
    apply False.elim assump_10
  let assump_8 := assump_5 assump_16
  apply False.elim assump_8


variable (p7 p5 p2 p3 p1 p0 p6 : Prop)
theorem file5_38197 : ((((((p3 → p3) → False) → False) ∧ (((True ∧ True) → False) ∧ ((p6 → False) ∨ (False → p0)))) ∧ ((((p6 ∧ p5) ∧ (p7 ∨ p2)) ∧ ((p1 → p3) ∨ (False ∧ False))) → (((p7 → p6) ∨ (p5 ∨ p6)) → ((p7 → False) → (p6 ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_34 : (True ∧ True) := by
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_20 := assump_8 assump_34
          apply False.elim assump_20
        case inr assump_13 =>
          have assump_35 : (True ∧ True) := by
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_30 := assump_8 assump_35
          apply False.elim assump_30


variable (p6 p1 p3 p4 : Prop)
theorem file5_39177 : (((((p1 ∧ p6) → False) ∧ ((p3 ∨ p6) → False)) → False) → ((((p1 → False) → (False → p1)) → False) → (((False → False) → (True → False)) → ((False → p4) ∨ (False ∧ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inl
  intro assump_10
  apply False.elim assump_10


variable (p6 p0 p7 p2 p3 p4 p5 p1 : Prop)
theorem file5_39533 : (((((p4 → False) → (True ∧ p6)) ∨ ((p4 ∨ True) → (p7 → False))) → (((p3 → False) → False) ∧ ((p5 → p1) → (False ∨ False)))) → ((((p7 → p6) → False) → ((p6 ∧ p4) → (p7 ∨ p0))) ∨ (((p0 ∧ p3) → (p3 → False)) ∧ ((p3 ∨ p7) ∧ (p7 ∧ p2))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_21 : (p7 → p6) := by
      intro assump_15
      exact assump_6
    let assump_14 := assump_4 assump_21
    apply False.elim assump_14


variable (p6 p1 p0 p4 p7 p2 : Prop)
theorem file5_40101 : ((((((False ∨ p4) → (p2 → p7)) → ((p1 ∨ p7) ∧ (p7 ∧ p2))) ∧ (((False ∨ True) → False) ∧ ((p1 → False) → (p7 → p4)))) ∧ ((((p6 ∧ p1) ∨ (p7 ∧ p2)) → ((p0 ∨ True) ∨ (p0 ∨ p0))) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        have assump_43 : (((p6 ∧ p1) ∨ (p7 ∧ p2)) → ((p0 ∨ True) ∨ (p0 ∨ p0))) := by
          intro assump_25
          cases assump_25
          case inl assump_26 =>
            cases assump_26
            case intro assump_28 assump_29 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
          case inr assump_27 =>
            cases assump_27
            case intro assump_34 assump_35 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
        let assump_24 := assump_11 assump_43
        apply False.elim assump_24


variable (p0 p5 p4 p1 p6 p2 : Prop)
theorem file5_41149 : (((((True → False) → (p2 ∧ p6)) → False) ∧ (((p4 ∧ p1) ∨ (p4 → p4)) ∨ ((p5 ∨ p4) ∧ (p0 → True)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_105 : ((True → False) → (p2 ∧ p6)) := by
            intro assump_19
            apply And.intro
            have assump_106 : True := by
              apply True.intro
            let assump_22 := assump_19 assump_106
            apply False.elim assump_22
            have assump_107 : True := by
              apply True.intro
            let assump_28 := assump_19 assump_107
            apply False.elim assump_28
          let assump_18 := assump_2 assump_105
          apply False.elim assump_18
      case inr assump_9 =>
        have assump_108 : ((True → False) → (p2 ∧ p6)) := by
          intro assump_39
          apply And.intro
          have assump_109 : True := by
            apply True.intro
          let assump_42 := assump_39 assump_109
          apply False.elim assump_42
          have assump_110 : True := by
            apply True.intro
          let assump_48 := assump_39 assump_110
          apply False.elim assump_48
        let assump_38 := assump_2 assump_108
        apply False.elim assump_38
    case inr assump_7 =>
      cases assump_7
      case intro assump_55 assump_56 =>
        cases assump_55
        case inl assump_57 =>
          have assump_111 : ((True → False) → (p2 ∧ p6)) := by
            intro assump_66
            apply And.intro
            have assump_112 : True := by
              apply True.intro
            let assump_69 := assump_66 assump_112
            apply False.elim assump_69
            have assump_113 : True := by
              apply True.intro
            let assump_75 := assump_66 assump_113
            apply False.elim assump_75
          let assump_65 := assump_2 assump_111
          apply False.elim assump_65
        case inr assump_58 =>
          have assump_114 : ((True → False) → (p2 ∧ p6)) := by
            intro assump_89
            apply And.intro
            have assump_115 : True := by
              apply True.intro
            let assump_92 := assump_89 assump_115
            apply False.elim assump_92
            have assump_116 : True := by
              apply True.intro
            let assump_98 := assump_89 assump_116
            apply False.elim assump_98
          let assump_88 := assump_2 assump_114
          apply False.elim assump_88


variable (p4 p6 p7 p0 p5 p3 : Prop)
theorem file5_43818 : (((((p5 ∧ p5) → (p7 ∨ p0)) ∨ ((p7 ∨ p5) → (p6 ∨ False))) ∧ (((p4 ∨ p0) → False) ∧ ((p4 ∧ p3) ∧ (p7 ∧ p0)))) → ((((p7 ∧ False) ∧ (True ∨ False)) → ((False ∨ p6) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_16
            case intro assump_23 assump_24 =>
              have assump_65 : (p4 ∨ p0) := by
                apply Or.inl
                exact assump_17
              let assump_33 := assump_11 assump_65
              apply False.elim assump_33
    case inr assump_8 =>
      cases assump_6
      case intro assump_39 assump_40 =>
        cases assump_40
        case intro assump_43 assump_44 =>
          cases assump_43
          case intro assump_45 assump_46 =>
            cases assump_44
            case intro assump_51 assump_52 =>
              have assump_66 : (p4 ∨ p0) := by
                apply Or.inl
                exact assump_45
              let assump_61 := assump_39 assump_66
              apply False.elim assump_61


variable (p3 p6 p7 p5 p4 p2 p0 p1 : Prop)
theorem file5_45166 : (((((p3 ∨ p2) ∧ (True → False)) → ((p6 ∧ p6) → False)) ∨ (((p0 → False) → (p4 ∧ p0)) ∨ ((p1 → False) ∧ (p2 ∧ p3)))) ∨ ((((p2 ∧ p7) ∨ (p2 ∧ p5)) ∧ ((p6 ∧ p0) → False)) → (((p3 ∧ p7) → (p3 ∨ True)) → ((p1 ∧ p7) ∨ (p2 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        have assump_29 : True := by
          apply True.intro
        let assump_17 := assump_10 assump_29
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_30 : True := by
          apply True.intro
        let assump_25 := assump_10 assump_30
        apply False.elim assump_25


variable (p2 p1 p6 p3 p7 p4 : Prop)
theorem file5_45991 : (((((False ∧ p7) → False) ∨ ((p6 ∨ p4) → False)) ∨ (((True → False) → False) → ((True ∧ p2) → (p7 ∧ p4)))) ∨ ((((False → p2) → False) → ((p2 ∨ True) ∨ (p2 → False))) ∧ (((p1 → False) ∧ (p4 → False)) ∧ ((p6 → False) ∨ (p3 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2


variable (p1 p0 p3 p2 p4 p5 p6 p7 : Prop)
theorem file5_46440 : (((((False → False) → (p5 ∧ p2)) ∧ ((p6 ∨ False) → (p5 → p4))) → (((False ∧ False) → False) ∨ ((p4 → p5) ∨ (p4 → p0)))) ∨ ((((p3 → False) ∧ (p7 ∨ True)) → ((p5 ∨ True) ∨ (p0 → p5))) ∨ (((p5 ∨ p1) ∨ (p4 ∧ True)) ∨ ((p0 ∨ p2) ∨ (False → False))))) := by
  apply Or.inl
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    apply Or.inl
    intro assump_29
    cases assump_29
    case intro assump_30 assump_31 =>
      apply False.elim assump_30


variable (p2 p1 p6 p0 p4 p3 p5 : Prop)
theorem file5_46970 : (((((True ∨ p6) ∨ (False → p2)) ∨ ((True ∨ p1) ∨ (p0 → False))) ∨ (((p2 ∨ p2) ∧ (p1 ∧ p3)) → False)) ∨ ((((p5 ∧ p2) → False) ∨ ((p3 → False) ∨ (p4 → True))) ∨ (((p1 ∧ p5) ∨ (p5 ∧ p1)) ∧ ((p5 → True) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p4 p1 p7 p5 p0 p2 p6 p3 : Prop)
theorem file5_47347 : (((((True ∧ p3) → (True ∧ True)) → ((False ∧ p1) → False)) ∨ (((p2 → p0) → False) → False)) ∨ ((((p7 ∨ p2) → (p4 ∧ p1)) → ((p0 → p2) → (p5 ∧ p6))) ∧ (((p1 → p1) → False) → ((p3 → p1) → (p5 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p0 p2 p6 p3 : Prop)
theorem file5_47751 : (((((True → False) → False) ∧ ((False ∧ p3) ∨ (p2 → False))) ∨ (((True → False) ∧ (True ∨ True)) → False)) → ((((True → False) ∧ (p6 ∨ p6)) ∧ ((p2 ∧ p0) → False)) → (((False ∧ p6) → False) ∧ ((False ∧ p6) → False)))) := by
  intro assump_7
  intro assump_8
  apply And.intro
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    apply False.elim assump_10
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    apply False.elim assump_15


variable (p6 p2 p4 p1 p0 p7 p3 : Prop)
theorem file5_48293 : (((((p6 → p0) → (p0 → p4)) ∨ ((p1 ∨ False) ∧ (p7 → p3))) → False) → ((((p2 → False) ∧ (p1 ∧ p6)) ∧ ((False → False) ∧ (p4 ∧ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        cases assump_4
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            have assump_37 : (((p6 → p0) → (p0 → p4)) ∨ ((p1 ∨ False) ∧ (p7 → p3))) := by
              apply Or.inl
              intro assump_28
              intro assump_29
              exact assump_19
            let assump_27 := assump_1 assump_37
            apply False.elim assump_27


variable (p5 p0 p3 p4 p6 p7 p2 : Prop)
theorem file5_49131 : ((((((p2 ∨ p6) ∧ (p5 ∨ p3)) → ((p0 → p2) → False)) ∨ (((False → False) ∨ (p4 → False)) ∨ ((False → False) → False))) ∧ ((((p3 → True) → False) ∧ ((p4 ∨ p6) → (p3 ∨ p0))) ∧ (((p0 ∧ p5) ∧ (p0 ∧ p5)) → ((p7 → False) ∧ (p4 → False))))) → False) := by
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    cases assump_24
    case inl assump_26 =>
      cases assump_25
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          have assump_108 : (p3 → True) := by
            intro assump_43
            apply True.intro
          let assump_42 := assump_32 assump_108
          apply False.elim assump_42
    case inr assump_27 =>
      cases assump_27
      case inl assump_47 =>
        cases assump_47
        case inl assump_49 =>
          cases assump_25
          case intro assump_53 assump_54 =>
            cases assump_53
            case intro assump_55 assump_56 =>
              have assump_109 : (p3 → True) := by
                intro assump_66
                apply True.intro
              let assump_65 := assump_55 assump_109
              apply False.elim assump_65
        case inr assump_50 =>
          cases assump_25
          case intro assump_72 assump_73 =>
            cases assump_72
            case intro assump_74 assump_75 =>
              have assump_110 : (p3 → True) := by
                intro assump_85
                apply True.intro
              let assump_84 := assump_74 assump_110
              apply False.elim assump_84
      case inr assump_48 =>
        cases assump_25
        case intro assump_91 assump_92 =>
          cases assump_91
          case intro assump_93 assump_94 =>
            have assump_111 : (p3 → True) := by
              intro assump_104
              apply True.intro
            let assump_103 := assump_93 assump_111
            apply False.elim assump_103


variable (p0 p6 p1 p3 p5 p2 p7 p4 : Prop)
theorem file5_51107 : (((((p6 ∧ p1) ∨ (p7 ∧ p0)) ∨ ((p6 ∨ p2) ∨ (p7 ∧ p3))) → False) → ((((True → p0) ∧ (False ∨ False)) → ((p5 → p3) → (p2 → p4))) ∧ (((p6 ∧ True) → (p4 → False)) ∧ ((p2 ∧ p5) → (False → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_10
    case inl assump_13 =>
      apply False.elim assump_13
    case inr assump_14 =>
      apply False.elim assump_14
  apply And.intro
  intro assump_19
  intro assump_20
  cases assump_19
  case intro assump_23 assump_24 =>
    have assump_39 : (((p6 ∧ p1) ∨ (p7 ∧ p0)) ∨ ((p6 ∨ p2) ∨ (p7 ∧ p3))) := by
      apply Or.inr
      apply Or.inl
      apply Or.inl
      exact assump_23
    let assump_31 := assump_1 assump_39
    apply False.elim assump_31
  intro assump_35
  intro assump_36
  apply False.elim assump_36


variable (p5 p3 p2 p1 p4 p0 : Prop)
theorem file5_52044 : ((((((p0 → True) → False) → ((p4 ∨ p5) ∧ (p2 → p2))) ∨ (((p4 → p2) → False) → ((p3 ∨ p1) → (p2 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p0 → True) → False) → ((p4 ∨ p5) ∧ (p2 → p2))) ∨ (((p4 → p2) → False) → ((p3 ∨ p1) → (p2 ∨ p2)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    have assump_22 : (p0 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_22
    apply False.elim assump_8
    intro assump_13
    exact assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p1 p7 p5 p3 p6 : Prop)
theorem file5_52686 : ((((((p5 → False) → (p7 ∨ p1)) → False) ∧ (((False → False) ∧ (p6 → False)) → ((p3 ∧ p1) → False))) ∧ ((((p1 ∧ False) ∨ (p6 ∨ p3)) → ((False → True) ∨ (True ∧ p1))) → False)) → False) := by
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_36 : (((p1 ∧ False) ∨ (p6 ∨ p3)) → ((False → True) ∨ (True ∧ p1))) := by
        intro assump_16
        cases assump_16
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
        case inr assump_18 =>
          cases assump_18
          case inl assump_25 =>
            apply Or.inl
            intro assump_29
            apply True.intro
          case inr assump_26 =>
            apply Or.inl
            intro assump_32
            apply True.intro
      let assump_15 := assump_6 assump_36
      apply False.elim assump_15


variable (p7 p6 p3 p1 p2 p5 p0 : Prop)
theorem file5_53699 : (((((p1 → True) → (p7 ∨ p1)) → ((True → p0) ∨ (False ∨ p6))) ∧ (((p0 ∨ p3) ∧ (p2 ∧ p5)) ∧ ((True → False) ∧ (False ∧ p0)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            cases assump_7
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
        case inr assump_11 =>
          cases assump_9
          case intro assump_30 assump_31 =>
            cases assump_7
            case intro assump_36 assump_37 =>
              cases assump_37
              case intro assump_40 assump_41 =>
                apply False.elim assump_40


variable (p5 p4 p7 p6 p2 p3 : Prop)
theorem file5_54689 : ((((((p2 ∧ p6) → (p2 → p3)) → ((p4 ∧ True) ∨ (False → False))) ∨ (((p4 → p5) → False) ∧ ((p2 ∧ True) ∨ (p7 → p2)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 ∧ p6) → (p2 → p3)) → ((p4 ∧ True) ∨ (False → False))) ∨ (((p4 → p5) → False) ∧ ((p2 ∧ True) ∨ (p7 → p2)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p3 p0 p4 p1 : Prop)
theorem file5_55209 : (((((False → False) → False) → False) ∨ (((True → False) → False) → False)) ∨ ((((p5 → False) → False) ∨ ((p4 ∧ p0) ∨ (p5 → False))) ∨ (((p3 ∨ p5) ∧ (p1 ∨ p3)) ∨ ((p5 → False) ∧ (True → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → False) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p0 p5 p3 p7 p1 : Prop)
theorem file5_55674 : ((((((p1 → False) ∧ (p7 → False)) ∨ ((False → False) → False)) → (((p0 ∨ p3) → False) ∨ ((p7 ∧ True) → (False → False)))) ∧ ((((p5 ∧ False) ∧ (False ∧ p6)) ∨ ((False ∧ p5) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p5 ∧ False) ∧ (False ∧ p6)) ∨ ((False ∧ p5) → False)) := by
      apply Or.inr
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p3 p6 p1 p0 p2 p7 : Prop)
theorem file5_56298 : (((((p7 ∧ p1) ∧ (p7 → False)) ∨ ((p3 ∧ False) ∨ (p2 → False))) → (((p7 ∧ p6) ∧ (p6 → False)) → ((p2 ∨ p0) → False))) ∨ ((((True → p7) ∨ (False ∧ p2)) → ((p7 ∧ p1) ∨ (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_1
        case inl assump_18 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              have assump_91 : p7 := by
                exact assump_22
              let assump_30 := assump_21 assump_91
              apply False.elim assump_30
        case inr assump_19 =>
          cases assump_19
          case inl assump_34 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              apply False.elim assump_37
          case inr assump_35 =>
            have assump_92 : p2 := by
              exact assump_4
            let assump_44 := assump_35 assump_92
            apply False.elim assump_44
  case inr assump_5 =>
    cases assump_2
    case intro assump_50 assump_51 =>
      cases assump_50
      case intro assump_52 assump_53 =>
        cases assump_1
        case inl assump_60 =>
          cases assump_60
          case intro assump_62 assump_63 =>
            cases assump_62
            case intro assump_64 assump_65 =>
              have assump_93 : p7 := by
                exact assump_64
              let assump_72 := assump_63 assump_93
              apply False.elim assump_72
        case inr assump_61 =>
          cases assump_61
          case inl assump_76 =>
            cases assump_76
            case intro assump_78 assump_79 =>
              apply False.elim assump_79
          case inr assump_77 =>
            have assump_94 : p6 := by
              exact assump_53
            let assump_87 := assump_51 assump_94
            apply False.elim assump_87


variable (p6 p5 p0 : Prop)
theorem file5_58412 : ((((((p6 ∧ p5) ∧ (p0 ∧ False)) ∧ ((p5 ∨ p5) → False)) → False) → False) → False) := by
  intro assump_19
  have assump_43 : ((((p6 ∧ p5) ∧ (p0 ∧ False)) ∧ ((p5 ∨ p5) → False)) → False) := by
    intro assump_23
    cases assump_23
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_27
          case intro assump_34 assump_35 =>
            apply False.elim assump_35
  let assump_22 := assump_19 assump_43
  apply False.elim assump_22


variable (p7 p1 p2 p4 p5 p3 p6 : Prop)
theorem file5_59049 : ((((((p7 → False) ∧ (p5 → False)) ∧ ((True ∧ False) ∧ (p2 ∨ p4))) ∧ (((p4 ∧ p1) ∨ (True → p3)) ∨ ((p3 → p6) ∨ (True ∨ True)))) ∧ ((((p3 → p7) → (p6 ∨ p6)) ∨ ((p3 → p1) → (p2 ∧ p6))) → (((False ∧ p7) → False) ∨ ((p4 → False) ∧ (p4 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17


variable (p1 p6 p5 p4 p0 : Prop)
theorem file5_59793 : ((((((True → False) ∨ (p5 ∨ True)) → ((True → False) → (p5 → False))) ∧ (((p1 ∨ p4) ∨ (p5 → True)) ∨ ((p6 ∨ p4) ∧ (p0 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((True → False) ∨ (p5 ∨ True)) → ((True → False) → (p5 → False))) ∧ (((p1 ∨ p4) ∨ (p5 → True)) ∨ ((p6 ∨ p4) ∧ (p0 ∧ p6)))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case inl assump_12 =>
      have assump_40 : True := by
        apply True.intro
      let assump_16 := assump_12 assump_40
      apply False.elim assump_16
    case inr assump_13 =>
      cases assump_13
      case inl assump_20 =>
        have assump_41 : True := by
          apply True.intro
        let assump_25 := assump_6 assump_41
        apply False.elim assump_25
      case inr assump_21 =>
        have assump_42 : True := by
          apply True.intro
        let assump_31 := assump_6 assump_42
        apply False.elim assump_31
    apply Or.inl
    apply Or.inr
    intro assump_35
    apply True.intro
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p5 p4 p1 p0 p2 p6 : Prop)
theorem file5_60956 : (((((p4 → False) ∨ (True → True)) ∨ ((p5 ∨ p2) ∧ (p0 → False))) ∧ (((False → p1) ∨ (p6 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_60 : ((False → p1) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_13
          apply False.elim assump_13
        let assump_12 := assump_3 assump_60
        apply False.elim assump_12
      case inr assump_7 =>
        have assump_61 : ((False → p1) ∨ (p6 → False)) := by
          apply Or.inl
          intro assump_24
          apply False.elim assump_24
        let assump_23 := assump_3 assump_61
        apply False.elim assump_23
    case inr assump_5 =>
      cases assump_5
      case intro assump_30 assump_31 =>
        cases assump_30
        case inl assump_32 =>
          have assump_62 : ((False → p1) ∨ (p6 → False)) := by
            apply Or.inl
            intro assump_41
            apply False.elim assump_41
          let assump_40 := assump_3 assump_62
          apply False.elim assump_40
        case inr assump_33 =>
          have assump_63 : ((False → p1) ∨ (p6 → False)) := by
            apply Or.inl
            intro assump_54
            apply False.elim assump_54
          let assump_53 := assump_3 assump_63
          apply False.elim assump_53


variable (p5 p7 p3 p6 p2 p0 : Prop)
theorem file5_62423 : ((((((True ∧ p0) → (True → p7)) ∧ ((p5 ∨ p2) ∨ (p5 → p3))) → (((True ∧ p7) → (p6 → False)) → ((p6 ∨ p5) ∨ (True ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((True ∧ p0) → (True → p7)) ∧ ((p5 ∨ p2) ∨ (p5 → p3))) → (((True ∧ p7) → (p6 → False)) → ((p6 ∨ p5) ∨ (True ∨ p2)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          apply Or.inl
          apply Or.inr
          exact assump_15
        case inr assump_16 =>
          apply Or.inr
          apply Or.inl
          apply True.intro
      case inr assump_14 =>
        apply Or.inr
        apply Or.inl
        apply True.intro
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p1 p6 p3 p7 p0 p2 p4 : Prop)
theorem file5_63325 : ((((((p0 ∧ p6) → (p1 ∧ p7)) → ((p2 → False) ∨ (False → False))) ∨ (((p0 ∧ p4) ∨ (p1 ∨ p6)) ∨ ((p2 → p4) → False))) ∧ ((((p7 ∨ p3) ∨ (p7 → False)) → ((p6 → False) → (p6 → False))) ∧ (((p6 ∧ False) ∧ (p3 → False)) ∨ ((p6 ∧ p1) ∧ (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
        case inr assump_13 =>
          cases assump_13
          case intro assump_22 assump_23 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              have assump_166 : p1 := by
                exact assump_25
              let assump_32 := assump_23 assump_166
              apply False.elim assump_32
    case inr assump_5 =>
      cases assump_5
      case inl assump_36 =>
        cases assump_36
        case inl assump_38 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            cases assump_3
            case intro assump_46 assump_47 =>
              cases assump_47
              case inl assump_50 =>
                cases assump_50
                case intro assump_52 assump_53 =>
                  cases assump_52
                  case intro assump_54 assump_55 =>
                    apply False.elim assump_55
              case inr assump_51 =>
                cases assump_51
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    have assump_167 : p1 := by
                      exact assump_63
                    let assump_70 := assump_61 assump_167
                    apply False.elim assump_70
        case inr assump_39 =>
          cases assump_39
          case inl assump_74 =>
            cases assump_3
            case intro assump_78 assump_79 =>
              cases assump_79
              case inl assump_82 =>
                cases assump_82
                case intro assump_84 assump_85 =>
                  cases assump_84
                  case intro assump_86 assump_87 =>
                    apply False.elim assump_87
              case inr assump_83 =>
                cases assump_83
                case intro assump_92 assump_93 =>
                  cases assump_92
                  case intro assump_94 assump_95 =>
                    have assump_168 : p1 := by
                      exact assump_95
                    let assump_102 := assump_93 assump_168
                    apply False.elim assump_102
          case inr assump_75 =>
            cases assump_3
            case intro assump_108 assump_109 =>
              cases assump_109
              case inl assump_112 =>
                cases assump_112
                case intro assump_114 assump_115 =>
                  cases assump_114
                  case intro assump_116 assump_117 =>
                    apply False.elim assump_117
              case inr assump_113 =>
                cases assump_113
                case intro assump_122 assump_123 =>
                  cases assump_122
                  case intro assump_124 assump_125 =>
                    have assump_169 : p1 := by
                      exact assump_125
                    let assump_132 := assump_123 assump_169
                    apply False.elim assump_132
      case inr assump_37 =>
        cases assump_3
        case intro assump_138 assump_139 =>
          cases assump_139
          case inl assump_142 =>
            cases assump_142
            case intro assump_144 assump_145 =>
              cases assump_144
              case intro assump_146 assump_147 =>
                apply False.elim assump_147
          case inr assump_143 =>
            cases assump_143
            case intro assump_152 assump_153 =>
              cases assump_152
              case intro assump_154 assump_155 =>
                have assump_170 : p1 := by
                  exact assump_155
                let assump_162 := assump_153 assump_170
                apply False.elim assump_162


variable (p6 p2 p3 p5 p4 : Prop)
theorem file5_67702 : (((((p2 → True) ∨ (p6 ∨ p2)) ∨ ((p2 ∨ False) → False)) ∨ (((p4 → p3) → (p2 → False)) → False)) ∨ ((((p3 ∧ True) → (p3 ∧ p4)) → False) ∧ (((p5 → p5) → (True → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply True.intro


variable (p4 p6 p3 p7 p1 p2 : Prop)
theorem file5_68041 : ((((((p7 → False) ∧ (p2 → False)) ∨ ((p1 ∨ p2) ∧ (p3 → False))) → (((p4 ∧ p6) ∧ (False ∧ p4)) → ((p6 → p3) → (p4 → False)))) ∧ ((((p3 → False) ∧ (False ∨ p3)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (((p3 → False) ∧ (False ∨ p3)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          have assump_29 : p3 := by
            exact assump_15
          let assump_21 := assump_10 assump_29
          apply False.elim assump_21
    let assump_8 := assump_3 assump_28
    apply False.elim assump_8


variable (p0 p3 p4 p2 p1 p6 p5 : Prop)
theorem file5_68852 : (((((p5 → False) ∧ (p2 ∧ p5)) → False) → (((p4 → False) → False) → False)) → ((((True ∨ p0) ∨ (p3 → p5)) ∧ ((p1 ∧ p1) ∧ (p2 ∨ p2))) ∨ (((True ∧ True) ∧ (p0 → False)) → ((p4 ∧ p6) → (p5 ∨ True))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply Or.inr
        apply True.intro


variable (p4 p3 p5 p0 p6 p1 p2 : Prop)
theorem file5_69400 : (((((False ∨ p3) → (p4 → False)) → ((False ∧ False) → (p4 → p5))) → False) → ((((p0 → False) ∧ (p2 ∨ p4)) → ((p6 → False) → (p2 → False))) ∧ (((p1 → False) → (False → p1)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_10
    case inl assump_13 =>
      have assump_67 : (((False ∨ p3) → (p4 → False)) → ((False ∧ False) → (p4 → p5))) := by
        intro assump_20
        intro assump_21
        intro assump_22
        cases assump_21
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
      let assump_19 := assump_1 assump_67
      apply False.elim assump_19
    case inr assump_14 =>
      have assump_68 : (((False ∨ p3) → (p4 → False)) → ((False ∧ False) → (p4 → p5))) := by
        intro assump_37
        intro assump_38
        intro assump_39
        cases assump_38
        case intro assump_42 assump_43 =>
          apply False.elim assump_42
      let assump_36 := assump_1 assump_68
      apply False.elim assump_36
  intro assump_49
  have assump_69 : (((False ∨ p3) → (p4 → False)) → ((False ∧ False) → (p4 → p5))) := by
    intro assump_55
    intro assump_56
    intro assump_57
    cases assump_56
    case intro assump_60 assump_61 =>
      apply False.elim assump_60
  let assump_54 := assump_1 assump_69
  apply False.elim assump_54


variable (p4 p5 : Prop)
theorem file5_70858 : (((((p5 ∨ p4) → False) → ((p4 ∧ p4) → (True → False))) → False) → False) := by
  intro assump_1
  have assump_25 : (((p5 ∨ p4) → False) → ((p4 ∧ p4) → (True → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      have assump_26 : (p5 ∨ p4) := by
        apply Or.inr
        exact assump_11
      let assump_18 := assump_5 assump_26
      apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p7 p3 p0 p6 p4 p2 : Prop)
theorem file5_71433 : (((((False → p2) → False) → False) ∨ (((p0 → False) ∧ (p3 → False)) ∨ ((p4 → False) ∧ (p7 ∧ p0)))) ∨ ((((True ∨ p4) ∧ (p1 ∧ p2)) ∧ ((p2 → p6) → (False ∨ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_11
  have assump_21 : (False → p2) := by
    intro assump_15
    apply False.elim assump_15
  let assump_14 := assump_11 assump_21
  apply False.elim assump_14


variable (p1 p0 p2 p4 p7 : Prop)
theorem file5_71870 : ((((((p7 ∨ p1) → (p4 ∧ False)) → ((p7 ∧ p2) → (p7 ∧ p2))) ∨ (((p7 → False) ∧ (p0 ∨ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p7 ∨ p1) → (p4 ∧ False)) → ((p7 ∧ p2) → (p7 ∧ p2))) ∨ (((p7 → False) ∧ (p0 ∨ True)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      exact assump_7
    cases assump_6
    case intro assump_15 assump_16 =>
      exact assump_16
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p4 p2 p0 p3 p7 p6 : Prop)
theorem file5_72489 : (((((p0 → p2) ∨ (p7 ∨ p6)) ∧ ((p2 ∧ p7) ∧ (p4 ∧ False))) ∧ (((False → False) ∧ (p3 → False)) → False)) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_11
            case intro assump_18 assump_19 =>
              apply False.elim assump_19
      case inr assump_7 =>
        cases assump_7
        case inl assump_24 =>
          cases assump_5
          case intro assump_28 assump_29 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              cases assump_29
              case intro assump_36 assump_37 =>
                apply False.elim assump_37
        case inr assump_25 =>
          cases assump_5
          case intro assump_44 assump_45 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              cases assump_45
              case intro assump_52 assump_53 =>
                apply False.elim assump_53


variable (p0 p1 p7 p6 p2 p5 p3 : Prop)
theorem file5_73729 : (((((False → False) → (p3 → p2)) ∧ ((False → p1) → False)) → (((p7 ∨ p6) ∧ (p0 → False)) ∨ ((False → False) → (p7 → p2)))) ∨ ((((p1 → False) ∧ (p2 ∧ p5)) → ((p3 ∨ p2) → False)) ∧ (((p5 → False) → False) → False))) := by
  apply Or.inl
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    apply Or.inr
    intro assump_15
    intro assump_16
    have assump_30 : (False → p1) := by
      intro assump_24
      apply False.elim assump_24
    let assump_23 := assump_10 assump_30
    apply False.elim assump_23


variable (p1 p6 p2 : Prop)
theorem file5_74308 : (((((True ∨ p2) ∧ (p6 → p6)) ∧ ((p2 → False) → (True ∨ p1))) → False) → False) := by
  intro assump_1
  have assump_14 : (((True ∨ p2) ∧ (p6 → p6)) ∧ ((p2 → False) → (True ∨ p1))) := by
    apply And.intro
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_5
    exact assump_5
    intro assump_8
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p6 p0 p1 p2 p3 p4 : Prop)
theorem file5_74795 : (((((p2 → False) → False) ∧ ((p4 → p7) ∧ (p0 ∨ p1))) ∧ (((False ∧ False) ∨ (False ∧ False)) ∧ ((p2 ∨ p7) → False))) → ((((p0 → False) → False) → False) → (((p3 → False) ∨ (p6 ∨ True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_17
          case inl assump_20 =>
            cases assump_11
            case intro assump_24 assump_25 =>
              cases assump_24
              case inl assump_26 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  apply False.elim assump_28
              case inr assump_27 =>
                cases assump_27
                case intro assump_32 assump_33 =>
                  apply False.elim assump_32
          case inr assump_21 =>
            cases assump_11
            case intro assump_38 assump_39 =>
              cases assump_38
              case inl assump_40 =>
                cases assump_40
                case intro assump_42 assump_43 =>
                  apply False.elim assump_42
              case inr assump_41 =>
                cases assump_41
                case intro assump_46 assump_47 =>
                  apply False.elim assump_46
  case inr assump_5 =>
    cases assump_5
    case inl assump_50 =>
      cases assump_1
      case intro assump_56 assump_57 =>
        cases assump_56
        case intro assump_58 assump_59 =>
          cases assump_59
          case intro assump_62 assump_63 =>
            cases assump_63
            case inl assump_66 =>
              cases assump_57
              case intro assump_70 assump_71 =>
                cases assump_70
                case inl assump_72 =>
                  cases assump_72
                  case intro assump_74 assump_75 =>
                    apply False.elim assump_74
                case inr assump_73 =>
                  cases assump_73
                  case intro assump_78 assump_79 =>
                    apply False.elim assump_78
            case inr assump_67 =>
              cases assump_57
              case intro assump_84 assump_85 =>
                cases assump_84
                case inl assump_86 =>
                  cases assump_86
                  case intro assump_88 assump_89 =>
                    apply False.elim assump_88
                case inr assump_87 =>
                  cases assump_87
                  case intro assump_92 assump_93 =>
                    apply False.elim assump_92
    case inr assump_51 =>
      cases assump_1
      case intro assump_100 assump_101 =>
        cases assump_100
        case intro assump_102 assump_103 =>
          cases assump_103
          case intro assump_106 assump_107 =>
            cases assump_107
            case inl assump_110 =>
              cases assump_101
              case intro assump_114 assump_115 =>
                cases assump_114
                case inl assump_116 =>
                  cases assump_116
                  case intro assump_118 assump_119 =>
                    apply False.elim assump_118
                case inr assump_117 =>
                  cases assump_117
                  case intro assump_122 assump_123 =>
                    apply False.elim assump_122
            case inr assump_111 =>
              cases assump_101
              case intro assump_128 assump_129 =>
                cases assump_128
                case inl assump_130 =>
                  cases assump_130
                  case intro assump_132 assump_133 =>
                    apply False.elim assump_132
                case inr assump_131 =>
                  cases assump_131
                  case intro assump_136 assump_137 =>
                    apply False.elim assump_136


variable (p3 p0 p7 p1 p2 p6 : Prop)
theorem file5_78809 : (((((False ∧ p0) ∧ (p1 → False)) → False) → (((p7 ∧ p6) → (p6 ∧ p7)) ∨ ((p0 ∨ p1) → (False ∨ p7)))) ∨ ((((p2 → False) → (p6 → False)) → False) ∧ (((p2 ∧ p6) ∧ (p3 → False)) ∨ ((p1 → p7) → (p6 ∨ p2))))) := by
  apply Or.inl
  intro assump_5
  apply Or.inl
  intro assump_8
  apply And.intro
  cases assump_8
  case intro assump_9 assump_10 =>
    exact assump_10
  cases assump_8
  case intro assump_15 assump_16 =>
    exact assump_15


variable (p0 p7 p4 p6 : Prop)
theorem file5_79298 : (((((p7 ∨ False) → False) ∧ ((p0 → False) → False)) ∧ (((p6 → True) ∨ (p7 ∨ p6)) → False)) → ((((True ∨ p7) → False) ∨ ((p7 ∨ p6) → (False ∧ p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_39 : ((p6 → True) ∨ (p7 ∨ p6)) := by
          apply Or.inl
          intro assump_18
          apply True.intro
        let assump_17 := assump_8 assump_39
        apply False.elim assump_17
  case inr assump_4 =>
    cases assump_1
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        have assump_40 : ((p6 → True) ∨ (p7 ∨ p6)) := by
          apply Or.inl
          intro assump_35
          apply True.intro
        let assump_34 := assump_25 assump_40
        apply False.elim assump_34


variable (p5 p6 p7 p2 p3 : Prop)
theorem file5_80274 : ((((((False → False) → (p3 ∨ False)) ∨ ((p5 → p3) → (p7 → p3))) → (((p6 ∧ p5) ∧ (p2 ∧ False)) → False)) → ((((False ∨ False) ∧ (False → False)) → False) → False)) → False) := by
  intro assump_11
  have assump_44 : ((((False → False) → (p3 ∨ False)) ∨ ((p5 → p3) → (p7 → p3))) → (((p6 ∧ p5) ∧ (p2 ∧ False)) → False)) := by
    intro assump_15
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_18
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
  let assump_14 := assump_11 assump_44
  have assump_45 : (((False ∨ False) ∧ (False → False)) → False) := by
    intro assump_32
    cases assump_32
    case intro assump_33 assump_34 =>
      cases assump_33
      case inl assump_35 =>
        apply False.elim assump_35
      case inr assump_36 =>
        apply False.elim assump_36
  let assump_31 := assump_14 assump_45
  apply False.elim assump_31


variable (p2 p0 p7 p5 p1 p6 p4 : Prop)
theorem file5_81327 : ((((((p7 ∨ p7) ∨ (p2 ∨ True)) → False) → (((p6 ∧ False) ∧ (p0 ∨ p6)) → False)) ∧ ((((p1 → True) → False) ∧ ((p6 ∨ p7) ∨ (True → False))) ∧ (((p5 ∨ p1) ∨ (False ∨ p0)) ∧ ((p4 → p4) → False)))) → False) := by
  intro assump_95
  cases assump_95
  case intro assump_96 assump_97 =>
    cases assump_97
    case intro assump_100 assump_101 =>
      cases assump_100
      case intro assump_102 assump_103 =>
        cases assump_103
        case inl assump_106 =>
          cases assump_106
          case inl assump_108 =>
            cases assump_101
            case intro assump_112 assump_113 =>
              cases assump_112
              case inl assump_114 =>
                cases assump_114
                case inl assump_116 =>
                  have assump_245 : (p4 → p4) := by
                    intro assump_123
                    exact assump_123
                  let assump_122 := assump_113 assump_245
                  apply False.elim assump_122
                case inr assump_117 =>
                  have assump_246 : (p4 → p4) := by
                    intro assump_134
                    exact assump_134
                  let assump_133 := assump_113 assump_246
                  apply False.elim assump_133
              case inr assump_115 =>
                cases assump_115
                case inl assump_140 =>
                  apply False.elim assump_140
                case inr assump_141 =>
                  have assump_247 : (p4 → p4) := by
                    intro assump_149
                    exact assump_149
                  let assump_148 := assump_113 assump_247
                  apply False.elim assump_148
          case inr assump_109 =>
            cases assump_101
            case intro assump_157 assump_158 =>
              cases assump_157
              case inl assump_159 =>
                cases assump_159
                case inl assump_161 =>
                  have assump_248 : (p4 → p4) := by
                    intro assump_168
                    exact assump_168
                  let assump_167 := assump_158 assump_248
                  apply False.elim assump_167
                case inr assump_162 =>
                  have assump_249 : (p4 → p4) := by
                    intro assump_179
                    exact assump_179
                  let assump_178 := assump_158 assump_249
                  apply False.elim assump_178
              case inr assump_160 =>
                cases assump_160
                case inl assump_185 =>
                  apply False.elim assump_185
                case inr assump_186 =>
                  have assump_250 : (p4 → p4) := by
                    intro assump_194
                    exact assump_194
                  let assump_193 := assump_158 assump_250
                  apply False.elim assump_193
        case inr assump_107 =>
          cases assump_101
          case intro assump_202 assump_203 =>
            cases assump_202
            case inl assump_204 =>
              cases assump_204
              case inl assump_206 =>
                have assump_251 : (p4 → p4) := by
                  intro assump_213
                  exact assump_213
                let assump_212 := assump_203 assump_251
                apply False.elim assump_212
              case inr assump_207 =>
                have assump_252 : (p4 → p4) := by
                  intro assump_224
                  exact assump_224
                let assump_223 := assump_203 assump_252
                apply False.elim assump_223
            case inr assump_205 =>
              cases assump_205
              case inl assump_230 =>
                apply False.elim assump_230
              case inr assump_231 =>
                have assump_253 : (p4 → p4) := by
                  intro assump_239
                  exact assump_239
                let assump_238 := assump_203 assump_253
                apply False.elim assump_238


variable (p7 p2 p5 p4 p3 p0 p6 p1 : Prop)
theorem file5_85343 : ((((((p3 ∨ p6) → False) → ((p1 ∨ p4) ∧ (p1 ∨ p6))) → (((p3 ∨ p6) ∨ (p3 → False)) → ((p7 → False) ∨ (p1 → False)))) ∧ ((((p5 ∨ p1) ∨ (p6 → p7)) → False) ∧ (((p2 ∧ p2) ∧ (False ∧ p0)) ∧ ((p0 ∨ p5) → (p5 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              apply False.elim assump_20


variable (p0 p2 p3 : Prop)
theorem file5_86058 : (((((p2 → p3) ∧ (False ∧ p0)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((p2 → p3) ∧ (False ∧ p0)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p1 p4 p3 p6 p7 : Prop)
theorem file5_86495 : ((((((p1 ∨ p4) ∧ (False ∧ False)) ∨ ((False → p3) ∧ (p6 → p6))) ∨ (((p5 ∨ p7) → False) → ((True → True) ∨ (p6 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p1 ∨ p4) ∧ (False ∧ False)) ∨ ((False → p3) ∧ (p6 → p6))) ∨ (((p5 ∨ p7) → False) → ((True → True) ∨ (p6 ∧ p7)))) := by
    apply Or.inl
    apply Or.inr
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p3 p1 p5 p0 p2 p4 : Prop)
theorem file5_87066 : (((((p6 → False) → (True ∨ True)) → False) → False) ∨ ((((True → p6) ∧ (p1 → p5)) ∨ ((False → p3) ∧ (True ∨ p4))) → (((p3 ∧ p0) → (p2 → False)) ∧ ((p5 → p6) ∨ (False ∨ False))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p6 → False) → (True ∨ True)) := by
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p6 p1 p3 : Prop)
theorem file5_87515 : ((((((True → False) ∧ (p1 ∧ p6)) → ((p4 ∨ p6) → (p4 ∧ p3))) ∨ (((False ∨ p1) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_80 : ((((True → False) ∧ (p1 ∧ p6)) → ((p4 ∨ p6) → (p4 ∧ p3))) ∨ (((False ∨ p1) → False) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          exact assump_7
    case inr assump_8 =>
      cases assump_5
      case intro assump_23 assump_24 =>
        cases assump_24
        case intro assump_27 assump_28 =>
          have assump_81 : True := by
            apply True.intro
          let assump_35 := assump_23 assump_81
          apply False.elim assump_35
    cases assump_6
    case inl assump_39 =>
      cases assump_5
      case intro assump_43 assump_44 =>
        cases assump_44
        case intro assump_47 assump_48 =>
          have assump_82 : True := by
            apply True.intro
          let assump_55 := assump_43 assump_82
          apply False.elim assump_55
    case inr assump_40 =>
      cases assump_5
      case intro assump_61 assump_62 =>
        cases assump_62
        case intro assump_65 assump_66 =>
          have assump_83 : True := by
            apply True.intro
          let assump_73 := assump_61 assump_83
          apply False.elim assump_73
  let assump_4 := assump_1 assump_80
  apply False.elim assump_4


variable (p5 p1 p7 p6 p3 p4 p0 : Prop)
theorem file5_89100 : ((((((False → False) ∨ (p3 → False)) → False) → (((p5 → False) → (p4 ∧ True)) ∧ ((p0 ∧ p5) → (p1 → False)))) → ((((p7 → p3) ∧ (p7 ∧ False)) → False) → (((True → False) ∧ (p0 → p6)) ∧ ((p6 → True) → (p4 → p4))))) → False) := by
  intro assump_17
  have assump_71 : ((((False → False) ∨ (p3 → False)) → False) → (((p5 → False) → (p4 ∧ True)) ∧ ((p0 ∧ p5) → (p1 → False)))) := by
    intro assump_21
    apply And.intro
    intro assump_22
    apply And.intro
    have assump_72 : ((False → False) ∨ (p3 → False)) := by
      apply Or.inl
      intro assump_28
      apply False.elim assump_28
    let assump_27 := assump_21 assump_72
    apply False.elim assump_27
    apply True.intro
    intro assump_34
    intro assump_35
    cases assump_34
    case intro assump_38 assump_39 =>
      have assump_73 : ((False → False) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_47
        apply False.elim assump_47
      let assump_46 := assump_21 assump_73
      apply False.elim assump_46
  let assump_20 := assump_17 assump_71
  have assump_74 : (((p7 → p3) ∧ (p7 ∧ False)) → False) := by
    intro assump_54
    cases assump_54
    case intro assump_55 assump_56 =>
      cases assump_56
      case intro assump_59 assump_60 =>
        apply False.elim assump_60
  let assump_53 := assump_20 assump_74
  let assump_65 := And.left assump_53
  let assump_66 := And.left assump_65
  have assump_75 : True := by
    apply True.intro
  let assump_67 := assump_66 assump_75
  apply False.elim assump_67


variable (p0 p4 p1 p3 p2 p5 : Prop)
theorem file5_90670 : (((((p4 ∧ p2) → (p4 ∧ p4)) ∨ ((p0 → False) → False)) ∨ (((p0 ∨ True) → (p1 → p4)) → False)) ∨ ((((p0 ∧ p5) → False) → False) → (((False ∨ p2) → (p2 ∧ p0)) → ((p5 ∨ p3) ∨ (True ∨ p5))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    exact assump_2
  cases assump_1
  case intro assump_8 assump_9 =>
    exact assump_8


variable (p3 p4 : Prop)
theorem file5_91130 : (((((p4 ∨ False) ∨ (p4 → p3)) ∧ ((p4 → False) → (p4 → False))) → False) → False) := by
  intro assump_1
  have assump_36 : (((p4 ∨ False) ∨ (p4 → p3)) ∧ ((p4 → False) → (p4 → False))) := by
    apply And.intro
    apply Or.inr
    intro assump_5
    have assump_37 : (((p4 ∨ False) ∨ (p4 → p3)) ∧ ((p4 → False) → (p4 → False))) := by
      apply And.intro
      apply Or.inl
      apply Or.inl
      exact assump_5
      intro assump_10
      intro assump_11
      have assump_38 : p4 := by
        exact assump_11
      let assump_16 := assump_10 assump_38
      apply False.elim assump_16
    let assump_9 := assump_1 assump_37
    apply False.elim assump_9
    intro assump_23
    intro assump_24
    have assump_39 : p4 := by
      exact assump_24
    let assump_29 := assump_23 assump_39
    apply False.elim assump_29
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p4 p1 p7 p3 p6 p0 p5 : Prop)
theorem file5_92082 : (((((False ∧ p4) → False) → False) ∧ (((p0 ∧ p3) ∨ (False ∧ p6)) ∨ ((p0 ∨ p3) ∧ (p5 → p6)))) → ((((p7 ∧ p1) ∧ (p6 → p0)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_68 : ((False ∧ p4) → False) := by
            intro assump_22
            cases assump_22
            case intro assump_23 assump_24 =>
              apply False.elim assump_23
          let assump_21 := assump_5 assump_68
          apply False.elim assump_21
      case inr assump_12 =>
        cases assump_12
        case intro assump_30 assump_31 =>
          apply False.elim assump_30
    case inr assump_10 =>
      cases assump_10
      case intro assump_34 assump_35 =>
        cases assump_34
        case inl assump_36 =>
          have assump_69 : ((False ∧ p4) → False) := by
            intro assump_45
            cases assump_45
            case intro assump_46 assump_47 =>
              apply False.elim assump_46
          let assump_44 := assump_5 assump_69
          apply False.elim assump_44
        case inr assump_37 =>
          have assump_70 : ((False ∧ p4) → False) := by
            intro assump_60
            cases assump_60
            case intro assump_61 assump_62 =>
              apply False.elim assump_61
          let assump_59 := assump_5 assump_70
          apply False.elim assump_59


variable (p2 p5 p4 p0 p3 p6 p7 : Prop)
theorem file5_93684 : ((((((p0 → False) ∧ (p5 → False)) → False) ∧ (((True ∧ p5) ∧ (False ∧ p2)) ∧ ((p2 ∧ p5) → (p7 ∨ p6)))) ∧ ((((p4 → p3) ∧ (p5 → p4)) ∧ ((False → p5) ∨ (p0 ∨ False))) → (((p4 → False) ∧ (p5 ∨ p4)) ∧ ((p5 → False) ∨ (True → p3))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case intro assump_22 assump_23 =>
              apply False.elim assump_22


variable (p5 p1 p4 p6 p2 p3 p0 p7 : Prop)
theorem file5_94428 : (((((p3 → False) → (p3 ∨ p5)) ∨ ((p7 ∧ p4) ∨ (p1 ∧ False))) ∧ (((False → p1) → False) ∧ ((False ∨ p2) → (True → True)))) → ((((p4 → p2) → False) ∨ ((p7 → p6) ∧ (p7 → True))) ∨ (((p1 ∨ p0) ∧ (True ∧ p0)) ∨ ((p3 ∧ p1) → (p5 ∨ p4))))) := by
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply Or.inl
        intro assump_17
        have assump_62 : (False → p1) := by
          intro assump_23
          apply False.elim assump_23
        let assump_22 := assump_11 assump_62
        apply False.elim assump_22
    case inr assump_8 =>
      cases assump_8
      case inl assump_29 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_6
          case intro assump_37 assump_38 =>
            apply Or.inl
            apply Or.inl
            intro assump_43
            have assump_63 : (False → p1) := by
              intro assump_50
              apply False.elim assump_50
            let assump_49 := assump_37 assump_63
            apply False.elim assump_49
      case inr assump_30 =>
        cases assump_30
        case intro assump_56 assump_57 =>
          apply False.elim assump_57


variable (p1 p6 p0 p5 p4 p7 : Prop)
theorem file5_95777 : (((((p1 ∨ p7) → False) ∨ ((p4 → p7) → False)) ∧ (((p6 ∧ True) → False) → ((True → p0) → False))) → ((((p1 ∧ p7) ∨ (p5 → False)) → ((p4 → False) → (True ∨ p1))) ∨ (((p1 → False) → False) → ((p0 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      cases assump_10
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply Or.inl
          apply True.intro
      case inr assump_15 =>
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      apply Or.inl
      intro assump_28
      intro assump_29
      cases assump_28
      case inl assump_32 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          apply Or.inl
          apply True.intro
      case inr assump_33 =>
        apply Or.inl
        apply True.intro


variable (p7 p3 p1 p2 p4 p5 p6 p0 : Prop)
theorem file5_96806 : (((((False ∧ p4) ∨ (p1 → False)) ∧ ((False → p6) → False)) → (((p7 → p0) → False) ∨ ((p3 → p1) → False))) ∧ ((((p3 ∨ p4) ∨ (p4 ∧ p3)) → ((p3 ∧ p4) ∧ (p6 ∧ p3))) → (((False → False) → False) → ((p0 → p2) ∧ (True ∧ p5))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6
    case inr assump_5 =>
      apply Or.inl
      intro assump_14
      have assump_54 : (False → p6) := by
        intro assump_19
        apply False.elim assump_19
      let assump_18 := assump_3 assump_54
      apply False.elim assump_18
  intro assump_25
  intro assump_26
  apply And.intro
  intro assump_27
  have assump_55 : (False → False) := by
    intro assump_36
    apply False.elim assump_36
  let assump_35 := assump_26 assump_55
  apply False.elim assump_35
  apply And.intro
  apply True.intro
  have assump_56 : (False → False) := by
    intro assump_48
    apply False.elim assump_48
  let assump_47 := assump_26 assump_56
  apply False.elim assump_47


variable (p7 p6 p0 p2 p1 p3 p4 : Prop)
theorem file5_97990 : ((((((False → p3) ∨ (p4 ∨ p1)) ∧ ((p2 ∧ p7) → (p0 → p0))) ∨ (((p1 → p6) ∧ (p0 → False)) → ((p6 → p2) ∧ (False ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((False → p3) ∨ (p4 ∨ p1)) ∧ ((p2 ∧ p7) → (p0 → p0))) ∨ (((p1 → p6) ∧ (p0 → False)) → ((p6 → p2) ∧ (False ∨ p0)))) := by
    apply Or.inl
    apply And.intro
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      exact assump_9
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p3 p2 p4 p6 p0 p5 : Prop)
theorem file5_98639 : ((((((p2 → False) ∨ (p5 ∨ p3)) → False) ∧ (((p6 ∨ p4) → (p4 ∨ p6)) → False)) ∧ ((((True → False) → (False → False)) → ((True ∨ p0) → (p7 → p7))) → (((p5 ∧ p0) ∧ (p2 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_40 : ((p6 ∨ p4) → (p4 ∨ p6)) := by
        intro assump_30
        cases assump_30
        case inl assump_31 =>
          apply Or.inr
          exact assump_31
        case inr assump_32 =>
          apply Or.inl
          exact assump_32
      let assump_29 := assump_5 assump_40
      apply False.elim assump_29


variable (p4 p1 p6 p2 p7 p3 p5 : Prop)
theorem file5_99360 : (((((p4 ∨ p3) → False) ∧ ((p6 → p3) → False)) → (((p2 → p5) ∨ (p6 ∧ p5)) → ((False ∧ False) → False))) ∨ ((((p4 ∨ p1) ∨ (p4 ∨ p7)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4


variable (p2 p7 p0 p3 p4 p1 : Prop)
theorem file5_99723 : ((((((p7 → False) ∨ (p1 ∨ p1)) ∨ ((p2 ∨ p2) ∧ (p3 → False))) → (((p4 ∨ p0) ∧ (p7 ∧ False)) → False)) → ((((False → p4) → False) → False) → False)) → False) := by
  intro assump_5
  have assump_45 : ((((p7 → False) ∨ (p1 ∨ p1)) ∨ ((p2 ∨ p2) ∧ (p3 → False))) → (((p4 ∨ p0) ∧ (p7 ∧ False)) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_12
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
      case inr assump_14 =>
        cases assump_12
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
  let assump_8 := assump_5 assump_45
  have assump_46 : (((False → p4) → False) → False) := by
    intro assump_32
    have assump_47 : (False → p4) := by
      intro assump_36
      apply False.elim assump_36
    let assump_35 := assump_32 assump_47
    apply False.elim assump_35
  let assump_31 := assump_8 assump_46
  apply False.elim assump_31


variable (p7 p2 p5 p1 : Prop)
theorem file5_100810 : ((((((p5 → False) → (p2 → p7)) ∧ ((True ∧ True) → False)) → (((p5 → p2) ∧ (False → False)) → ((p1 ∧ False) ∧ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_61 : ((((p5 → False) → (p2 → p7)) ∧ ((True ∧ True) → False)) → (((p5 → p2) ∧ (False → False)) → ((p1 ∧ False) ∧ (True → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        have assump_62 : (True ∧ True) := by
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_19 := assump_14 assump_62
        apply False.elim assump_19
    cases assump_6
    case intro assump_23 assump_24 =>
      cases assump_5
      case intro assump_29 assump_30 =>
        have assump_63 : (True ∧ True) := by
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_35 := assump_30 assump_63
        apply False.elim assump_35
    intro assump_39
    cases assump_6
    case intro assump_42 assump_43 =>
      cases assump_5
      case intro assump_48 assump_49 =>
        have assump_64 : (True ∧ True) := by
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_54 := assump_49 assump_64
        apply False.elim assump_54
  let assump_4 := assump_1 assump_61
  apply False.elim assump_4


variable (p0 p4 p3 p2 p6 p1 p5 p7 : Prop)
theorem file5_102324 : (((((p1 ∧ False) → (p0 ∨ p2)) → ((True ∨ p7) ∨ (p7 → False))) ∨ (((p5 ∨ p1) ∨ (False → p4)) ∨ ((p6 → False) → (p4 → p6)))) ∨ ((((p3 → p0) → False) → ((p3 ∨ False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p5 p1 p3 p7 p6 p2 p0 : Prop)
theorem file5_102672 : (((((p7 ∧ False) → False) ∨ ((p7 ∨ True) → (True ∨ p7))) ∨ (((p3 → False) → (p1 → p5)) → ((p0 → False) ∧ (p7 ∧ p6)))) ∨ ((((p5 ∨ p2) ∧ (p5 ∧ p6)) ∧ ((p2 ∨ p0) → (False ∨ p0))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3


variable (p7 p3 p1 p6 p5 p4 : Prop)
theorem file5_103067 : (((((p6 → p6) ∧ (p5 ∧ False)) ∧ ((False ∧ p1) ∧ (p7 → p4))) ∧ (((p3 ∧ False) → False) → ((False ∨ p4) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_11


variable (p1 p2 p7 : Prop)
theorem file5_103530 : ((((((p1 ∧ False) ∧ (p7 → p1)) ∧ ((p2 → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p1 ∧ False) ∧ (p7 → p1)) ∧ ((p2 → False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


