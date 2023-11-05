variable (p6 p4 p0 : Prop)
theorem file8_35 : ((((((p6 ∨ p4) → False) → False) → (((p0 ∨ False) → (p4 → False)) → ((True ∧ True) ∨ (p0 → False)))) → False) → False) := by
  intro assump_26
  have assump_39 : ((((p6 ∨ p4) → False) → False) → (((p0 ∨ False) → (p4 → False)) → ((True ∧ True) ∨ (p0 → False)))) := by
    intro assump_30
    intro assump_31
    apply Or.inl
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_29 := assump_26 assump_39
  apply False.elim assump_29


variable (p0 p4 p5 p2 p1 p6 p3 : Prop)
theorem file8_552 : (((((True → False) ∧ (p1 → True)) ∧ ((p6 ∨ p4) ∨ (p3 ∧ False))) → (((p6 → True) ∨ (p3 ∨ p5)) → False)) ∨ ((((p5 ∧ p5) ∧ (p0 ∧ p6)) ∧ ((p4 ∨ p6) ∧ (p6 ∨ p5))) → (((p5 → False) ∧ (p5 ∨ p2)) ∨ ((p2 → False) → (False → p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case inl assump_15 =>
          cases assump_15
          case inl assump_17 =>
            have assump_115 : True := by
              apply True.intro
            let assump_23 := assump_9 assump_115
            apply False.elim assump_23
          case inr assump_18 =>
            have assump_116 : True := by
              apply True.intro
            let assump_31 := assump_9 assump_116
            apply False.elim assump_31
        case inr assump_16 =>
          cases assump_16
          case intro assump_35 assump_36 =>
            apply False.elim assump_36
  case inr assump_4 =>
    cases assump_4
    case inl assump_41 =>
      cases assump_1
      case intro assump_45 assump_46 =>
        cases assump_45
        case intro assump_47 assump_48 =>
          cases assump_46
          case inl assump_53 =>
            cases assump_53
            case inl assump_55 =>
              have assump_117 : True := by
                apply True.intro
              let assump_61 := assump_47 assump_117
              apply False.elim assump_61
            case inr assump_56 =>
              have assump_118 : True := by
                apply True.intro
              let assump_69 := assump_47 assump_118
              apply False.elim assump_69
          case inr assump_54 =>
            cases assump_54
            case intro assump_73 assump_74 =>
              apply False.elim assump_74
    case inr assump_42 =>
      cases assump_1
      case intro assump_81 assump_82 =>
        cases assump_81
        case intro assump_83 assump_84 =>
          cases assump_82
          case inl assump_89 =>
            cases assump_89
            case inl assump_91 =>
              have assump_119 : True := by
                apply True.intro
              let assump_97 := assump_83 assump_119
              apply False.elim assump_97
            case inr assump_92 =>
              have assump_120 : True := by
                apply True.intro
              let assump_105 := assump_83 assump_120
              apply False.elim assump_105
          case inr assump_90 =>
            cases assump_90
            case intro assump_109 assump_110 =>
              apply False.elim assump_110


variable (p6 p5 p3 p2 p1 p0 p4 : Prop)
theorem file8_3281 : (((((True ∧ p4) ∧ (p3 ∨ p1)) → ((p4 → p1) → False)) → (((p5 → p6) → (p2 → False)) ∧ ((p1 ∧ p6) ∨ (p4 → p4)))) → ((((p2 → False) ∨ (p1 ∨ False)) ∧ ((p0 ∧ False) ∧ (p0 → p4))) → (((p4 ∨ p2) ∨ (p2 ∨ p6)) → ((p0 → p2) → (False ∨ p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_2
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_14
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              apply False.elim assump_22
        case inr assump_16 =>
          cases assump_16
          case inl assump_27 =>
            cases assump_14
            case intro assump_31 assump_32 =>
              cases assump_31
              case intro assump_33 assump_34 =>
                apply False.elim assump_34
          case inr assump_28 =>
            apply False.elim assump_28
    case inr assump_10 =>
      cases assump_2
      case intro assump_43 assump_44 =>
        cases assump_43
        case inl assump_45 =>
          cases assump_44
          case intro assump_49 assump_50 =>
            cases assump_49
            case intro assump_51 assump_52 =>
              apply False.elim assump_52
        case inr assump_46 =>
          cases assump_46
          case inl assump_57 =>
            cases assump_44
            case intro assump_61 assump_62 =>
              cases assump_61
              case intro assump_63 assump_64 =>
                apply False.elim assump_64
          case inr assump_58 =>
            apply False.elim assump_58
  case inr assump_8 =>
    cases assump_8
    case inl assump_71 =>
      cases assump_2
      case intro assump_75 assump_76 =>
        cases assump_75
        case inl assump_77 =>
          cases assump_76
          case intro assump_81 assump_82 =>
            cases assump_81
            case intro assump_83 assump_84 =>
              apply False.elim assump_84
        case inr assump_78 =>
          cases assump_78
          case inl assump_89 =>
            cases assump_76
            case intro assump_93 assump_94 =>
              cases assump_93
              case intro assump_95 assump_96 =>
                apply False.elim assump_96
          case inr assump_90 =>
            apply False.elim assump_90
    case inr assump_72 =>
      cases assump_2
      case intro assump_105 assump_106 =>
        cases assump_105
        case inl assump_107 =>
          cases assump_106
          case intro assump_111 assump_112 =>
            cases assump_111
            case intro assump_113 assump_114 =>
              apply False.elim assump_114
        case inr assump_108 =>
          cases assump_108
          case inl assump_119 =>
            cases assump_106
            case intro assump_123 assump_124 =>
              cases assump_123
              case intro assump_125 assump_126 =>
                apply False.elim assump_126
          case inr assump_120 =>
            apply False.elim assump_120


variable (p7 p5 p2 p0 : Prop)
theorem file8_6485 : ((((((True ∨ p2) → False) ∧ ((False ∧ False) → (p0 ∨ p5))) → (((p5 → p2) ∧ (p0 ∧ True)) ∧ ((p7 → p0) ∧ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_62 : ((((True ∨ p2) → False) ∧ ((False ∧ False) → (p0 ∨ p5))) → (((p5 → p2) ∧ (p0 ∧ True)) ∧ ((p7 → p0) ∧ (p2 → False)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_63 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_16 := assump_9 assump_63
      apply False.elim assump_16
    apply And.intro
    cases assump_5
    case intro assump_20 assump_21 =>
      have assump_64 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_27 := assump_20 assump_64
      apply False.elim assump_27
    apply True.intro
    apply And.intro
    intro assump_31
    cases assump_5
    case intro assump_34 assump_35 =>
      have assump_65 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_41 := assump_34 assump_65
      apply False.elim assump_41
    intro assump_45
    cases assump_5
    case intro assump_48 assump_49 =>
      have assump_66 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_55 := assump_48 assump_66
      apply False.elim assump_55
  let assump_4 := assump_1 assump_62
  apply False.elim assump_4


variable (p1 p5 p3 p4 p6 : Prop)
theorem file8_7966 : (((((p5 → p5) ∧ (p3 ∨ p6)) ∧ ((True → True) → (p1 → p3))) → False) → ((((p3 → False) → False) ∧ ((False ∧ p3) → (p4 → p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_37 : (p3 → False) := by
      intro assump_17
      have assump_38 : (((p5 → p5) ∧ (p3 ∨ p6)) ∧ ((True → True) → (p1 → p3))) := by
        apply And.intro
        apply And.intro
        intro assump_22
        exact assump_22
        apply Or.inl
        exact assump_17
        intro assump_25
        intro assump_26
        exact assump_17
      let assump_21 := assump_1 assump_38
      apply False.elim assump_21
    let assump_16 := assump_3 assump_37
    apply False.elim assump_16


variable (p0 p5 p7 p4 p2 p3 p1 : Prop)
theorem file8_8760 : (((((True → False) → False) ∧ ((p1 ∨ False) ∨ (p2 → p7))) → False) → ((((p3 → p5) → False) → ((p2 → False) ∧ (p2 ∨ p1))) → (((p0 ∧ False) ∧ (p4 → p1)) ∨ ((p4 → p4) ∨ (p0 ∧ False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inr
  apply Or.inl
  intro assump_7
  exact assump_7


variable (p4 p1 p5 p0 p6 p7 p2 p3 : Prop)
theorem file8_9113 : ((((((p7 → p7) ∨ (True ∨ p7)) → ((p0 ∨ p4) → False)) ∧ (((p5 ∨ p7) → False) ∧ ((p7 → False) ∧ (False ∧ p7)))) ∧ ((((p6 ∧ p5) → False) → ((p0 → p1) ∨ (p3 ∧ p2))) → (((p6 → p1) → False) → False))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_19
      case intro assump_22 assump_23 =>
        cases assump_23
        case intro assump_26 assump_27 =>
          cases assump_27
          case intro assump_30 assump_31 =>
            apply False.elim assump_30


variable (p7 p3 p2 p5 p1 p6 p0 : Prop)
theorem file8_9753 : (((((p1 → False) ∧ (p5 → True)) → False) ∧ (((p5 ∧ p7) → (p3 ∨ p2)) → False)) → ((((p6 → p7) ∧ (True ∧ False)) → ((False ∧ False) → False)) ∨ (((p7 → False) ∨ (p1 ∨ p3)) → ((p6 ∧ p6) ∨ (p0 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10


variable (p5 p6 p0 p2 p3 p1 : Prop)
theorem file8_10234 : ((((((p1 ∨ p2) → (p5 → False)) ∨ ((p5 → False) → False)) → False) ∧ ((((p0 → p2) → (p3 ∧ p5)) → ((p0 ∨ p6) ∧ (False ∧ True))) ∧ (((p5 ∧ p0) → (True → False)) ∧ ((False ∨ True) → False)))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        have assump_28 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_24 := assump_19 assump_28
        apply False.elim assump_24


variable (p1 p0 p2 p4 p7 : Prop)
theorem file8_10860 : (((((False → False) → False) ∧ ((p1 ∧ p7) ∧ (p2 → p7))) → False) ∨ ((((p4 → p1) ∨ (p0 → p2)) ∨ ((p0 → p1) ∨ (False → p0))) ∧ (((p2 → False) ∨ (p2 → False)) → ((False ∧ p2) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_26 : (False → False) := by
          intro assump_20
          apply False.elim assump_20
        let assump_19 := assump_2 assump_26
        apply False.elim assump_19


variable (p5 p1 p6 p2 p4 p3 : Prop)
theorem file8_11496 : (((((p6 ∧ p4) → False) → False) → (((p5 ∨ p4) ∨ (p2 ∨ p5)) → ((p6 → False) → (False ∨ True)))) ∨ ((((p1 ∧ p4) → (p2 ∨ True)) ∧ ((True ∨ p2) → False)) ∨ (((p3 → p3) → (p5 → False)) ∧ ((False → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      apply Or.inr
      apply True.intro
    case inr assump_9 =>
      apply Or.inr
      apply True.intro
  case inr assump_7 =>
    cases assump_7
    case inl assump_18 =>
      apply Or.inr
      apply True.intro
    case inr assump_19 =>
      apply Or.inr
      apply True.intro


variable (p3 p0 p1 p2 p4 p7 p5 p6 : Prop)
theorem file8_12216 : (((((True → p3) → False) ∧ ((p6 ∧ True) ∨ (p3 ∨ p0))) → False) → ((((p5 ∨ p7) → (p1 ∨ True)) ∨ ((True ∧ p7) → (p6 ∧ p2))) ∨ (((True → False) ∨ (p4 ∨ p2)) ∧ ((p7 ∧ p0) ∨ (p2 ∧ p1))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply Or.inr
    apply True.intro
  case inr assump_6 =>
    apply Or.inr
    apply True.intro


variable (p2 p3 p6 p5 p1 p0 p4 p7 : Prop)
theorem file8_12674 : (((((False ∧ p4) ∧ (p4 ∨ p5)) → ((p0 ∧ p3) ∨ (p2 → p3))) ∨ (((p7 → False) ∨ (p1 → False)) ∧ ((p4 ∨ p6) → (False → False)))) ∨ ((((p3 → False) ∧ (p6 → p0)) ∧ ((p3 → False) → False)) ∧ (((p4 → p4) ∧ (False → p5)) ∨ ((True ∧ p6) ∨ (p0 ∧ False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      apply False.elim assump_11


variable (p6 p0 p3 p2 p1 p7 p5 : Prop)
theorem file8_13177 : (((((False ∨ True) ∨ (p7 ∨ p7)) ∨ ((p0 ∨ p5) ∨ (p1 → False))) → False) → ((((p1 ∧ False) ∨ (p6 ∧ p7)) → ((False ∧ p7) → False)) ∧ (((p3 ∨ p2) ∨ (p2 → False)) ∧ ((p1 ∨ True) ∧ (p0 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4
  apply And.intro
  apply Or.inr
  intro assump_10
  have assump_29 : (((False ∨ True) ∨ (p7 ∨ p7)) ∨ ((p0 ∨ p5) ∨ (p1 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_14 := assump_1 assump_29
  apply False.elim assump_14
  apply And.intro
  apply Or.inr
  apply True.intro
  intro assump_20
  have assump_30 : (((False ∨ True) ∨ (p7 ∨ p7)) ∨ ((p0 ∨ p5) ∨ (p1 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_25 := assump_1 assump_30
  apply False.elim assump_25


variable (p3 p4 p2 p1 p0 p6 : Prop)
theorem file8_14154 : (((((p1 ∧ False) ∧ (p2 ∨ p0)) ∧ ((p4 → False) ∧ (p1 ∧ p3))) → False) ∨ ((((p1 ∧ True) → False) ∨ ((p6 → p0) → (p6 ∧ p3))) → (((True → False) → False) → ((p3 → False) → (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7


variable (p7 p6 p4 p5 p3 : Prop)
theorem file8_14633 : ((((((p5 → p5) ∨ (False ∨ p5)) → False) → (((p6 ∧ p4) ∨ (False → p7)) ∧ ((p3 → False) ∧ (False → p4)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p5 → p5) ∨ (False ∨ p5)) → False) → (((p6 ∧ p4) ∨ (False → p7)) ∧ ((p3 → False) ∧ (False → p4)))) := by
    intro assump_5
    apply And.intro
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
    apply And.intro
    intro assump_11
    have assump_30 : ((p5 → p5) ∨ (False ∨ p5)) := by
      apply Or.inl
      intro assump_17
      exact assump_17
    let assump_16 := assump_5 assump_30
    apply False.elim assump_16
    intro assump_23
    apply False.elim assump_23
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p7 p4 p3 p5 p6 p0 : Prop)
theorem file8_15417 : (((((p7 ∧ p3) ∨ (p6 → p6)) → ((p1 ∧ p6) → (p7 ∨ True))) → False) → ((((False → False) → False) ∧ ((p7 → p7) → False)) ∨ (((p5 → p4) ∨ (p0 → p7)) → False))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_56 : (((p7 ∧ p3) ∨ (p6 → p6)) → ((p1 ∧ p6) → (p7 ∨ True))) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      cases assump_9
      case inl assump_17 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          apply Or.inl
          exact assump_19
      case inr assump_18 =>
        apply Or.inr
        apply True.intro
  let assump_8 := assump_1 assump_56
  apply False.elim assump_8
  intro assump_30
  have assump_57 : (((p7 ∧ p3) ∨ (p6 → p6)) → ((p1 ∧ p6) → (p7 ∨ True))) := by
    intro assump_35
    intro assump_36
    cases assump_36
    case intro assump_37 assump_38 =>
      cases assump_35
      case inl assump_43 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          apply Or.inl
          exact assump_45
      case inr assump_44 =>
        apply Or.inr
        apply True.intro
  let assump_34 := assump_1 assump_57
  apply False.elim assump_34


variable (p0 p5 p2 p4 p7 : Prop)
theorem file8_16683 : ((((((False → p7) ∨ (p5 → False)) → ((p0 → False) ∨ (p5 → False))) → (((p0 → True) ∧ (False → False)) ∨ ((p4 → p2) → (p2 → False)))) → False) → False) := by
  intro assump_28
  have assump_42 : ((((False → p7) ∨ (p5 → False)) → ((p0 → False) ∨ (p5 → False))) → (((p0 → True) ∧ (False → False)) ∨ ((p4 → p2) → (p2 → False)))) := by
    intro assump_32
    apply Or.inl
    apply And.intro
    intro assump_35
    apply True.intro
    intro assump_36
    apply False.elim assump_36
  let assump_31 := assump_28 assump_42
  apply False.elim assump_31


variable (p3 p1 p7 p5 p6 p4 p0 : Prop)
theorem file8_17294 : (((((p3 → p3) ∧ (p1 → False)) ∧ ((p4 ∧ p7) ∨ (True → False))) ∧ (((p0 ∧ p1) ∧ (p5 ∧ p6)) ∧ ((p6 → False) ∧ (False → False)))) → ((((p5 → False) ∨ (p3 → False)) → ((p4 ∧ p0) → (p5 ∨ p1))) → (((p4 → False) ∧ (p6 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_15
          case inl assump_22 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              cases assump_13
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  cases assump_32
                  case intro assump_34 assump_35 =>
                    cases assump_33
                    case intro assump_40 assump_41 =>
                      cases assump_31
                      case intro assump_46 assump_47 =>
                        have assump_86 : p6 := by
                          exact assump_41
                        let assump_53 := assump_46 assump_86
                        apply False.elim assump_53
          case inr assump_23 =>
            cases assump_13
            case intro assump_59 assump_60 =>
              cases assump_59
              case intro assump_61 assump_62 =>
                cases assump_61
                case intro assump_63 assump_64 =>
                  cases assump_62
                  case intro assump_69 assump_70 =>
                    cases assump_60
                    case intro assump_75 assump_76 =>
                      have assump_87 : p6 := by
                        exact assump_70
                      let assump_82 := assump_75 assump_87
                      apply False.elim assump_82


variable (p1 p4 p3 p5 p2 p0 : Prop)
theorem file8_19282 : ((((((True ∨ p5) → (p3 ∧ p2)) ∨ ((p4 ∨ p1) → False)) ∧ (((p0 ∨ p4) ∧ (p1 → False)) → False)) ∧ ((((p4 ∨ p1) ∧ (False ∧ True)) → False) → False)) → False) := by
  intro assump_43
  cases assump_43
  case intro assump_44 assump_45 =>
    cases assump_44
    case intro assump_46 assump_47 =>
      cases assump_46
      case inl assump_48 =>
        have assump_104 : (((p4 ∨ p1) ∧ (False ∧ True)) → False) := by
          intro assump_57
          cases assump_57
          case intro assump_58 assump_59 =>
            cases assump_58
            case inl assump_60 =>
              cases assump_59
              case intro assump_64 assump_65 =>
                apply False.elim assump_64
            case inr assump_61 =>
              cases assump_59
              case intro assump_70 assump_71 =>
                apply False.elim assump_70
        let assump_56 := assump_45 assump_104
        apply False.elim assump_56
      case inr assump_49 =>
        have assump_105 : (((p4 ∨ p1) ∧ (False ∧ True)) → False) := by
          intro assump_84
          cases assump_84
          case intro assump_85 assump_86 =>
            cases assump_85
            case inl assump_87 =>
              cases assump_86
              case intro assump_91 assump_92 =>
                apply False.elim assump_91
            case inr assump_88 =>
              cases assump_86
              case intro assump_97 assump_98 =>
                apply False.elim assump_97
        let assump_83 := assump_45 assump_105
        apply False.elim assump_83


variable (p6 p7 p3 p5 p4 : Prop)
theorem file8_20879 : ((((((p3 ∧ p7) → (p4 → True)) ∨ ((True → False) → (False → p7))) ∨ (((p3 ∨ p6) ∨ (p5 ∨ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_10 : ((((p3 ∧ p7) → (p4 → True)) ∨ ((True → False) → (False → p7))) ∨ (((p3 ∨ p6) ∨ (p5 ∨ True)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p6 p4 p5 p7 p0 p3 : Prop)
theorem file8_21369 : (((((p6 → True) → False) → False) ∨ (((True → p5) → False) → ((False ∧ p5) ∧ (p6 ∨ p5)))) → ((((p4 → False) → (True ∨ p7)) ∨ ((p4 ∧ p3) ∨ (p4 → p3))) ∨ (((p0 → False) ∧ (True → p0)) ∧ ((p6 ∨ p3) ∧ (p0 → p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply Or.inl
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_11
    apply Or.inl
    apply True.intro


variable (p7 p2 p0 p3 p6 p4 p1 p5 : Prop)
theorem file8_21915 : (((((p7 ∧ p7) → (p2 ∧ False)) ∨ ((p4 → False) ∧ (p5 ∧ p2))) → (((p2 ∧ p4) ∧ (p1 → p5)) → ((p7 ∧ p5) ∨ (p6 ∨ p4)))) ∧ ((((p4 → p6) → (False → False)) ∨ ((p4 ∨ p4) ∨ (p2 → p3))) ∨ (((p6 ∧ False) ∧ (p2 → p5)) ∧ ((False ∧ p0) ∧ (False → p6))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case inl assump_13 =>
        apply Or.inr
        apply Or.inr
        exact assump_6
      case inr assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          cases assump_18
          case intro assump_21 assump_22 =>
            apply Or.inr
            apply Or.inr
            exact assump_6
  apply Or.inl
  apply Or.inl
  intro assump_27
  intro assump_28
  apply False.elim assump_28


variable (p4 p1 p7 p2 p6 p5 p3 p0 : Prop)
theorem file8_22836 : (((((p5 ∧ False) → False) ∨ ((p3 ∨ p4) → (p7 ∨ True))) ∨ (((False ∨ p6) → False) → ((p3 ∧ p2) → (False → False)))) ∨ ((((p4 → p5) → (p0 ∨ p7)) → False) ∨ (((p7 ∧ p0) → (p7 ∨ p6)) → ((p1 ∨ p1) → (p3 → p2))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3


variable (p1 p0 p6 p2 p7 : Prop)
theorem file8_23250 : ((((((p7 ∨ p6) ∨ (p7 → p6)) ∨ ((p2 → False) ∧ (p0 ∨ p1))) ∨ (((p0 ∧ p6) → False) ∨ ((p7 ∨ p7) → (p0 → True)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p7 ∨ p6) ∨ (p7 → p6)) ∨ ((p2 → False) ∧ (p0 ∨ p1))) ∨ (((p0 ∧ p6) → False) ∨ ((p7 ∨ p7) → (p0 → True)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : ((((p7 ∨ p6) ∨ (p7 → p6)) ∨ ((p2 → False) ∧ (p0 ∨ p1))) ∨ (((p0 ∧ p6) → False) ∨ ((p7 ∨ p7) → (p0 → True)))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p3 p0 p5 p4 p7 p2 p1 : Prop)
theorem file8_24039 : (((((p5 ∨ p7) ∧ (p3 → p6)) ∧ ((p4 ∧ p2) ∨ (p1 → p2))) ∨ (((True ∨ p1) → False) → ((False → False) → False))) ∨ ((((p1 → True) → False) → False) ∨ (((p3 ∧ p0) → False) ∨ ((False ∧ p7) ∨ (p3 → p5))))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  have assump_11 : (True ∨ p1) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p1 p6 p4 p3 p0 p2 : Prop)
theorem file8_24508 : (((((p6 ∧ False) ∨ (True ∨ p4)) → False) ∨ (((True → False) → False) ∧ ((p4 → False) ∧ (p4 → p1)))) → ((((p0 ∧ p4) → (p3 ∧ p1)) ∨ ((p2 → p2) ∨ (p1 ∨ True))) ∨ (((p3 ∨ p6) ∧ (p1 ∧ False)) ∨ ((p3 ∨ p3) → (p4 → p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_66 : ((p6 ∧ False) ∨ (True ∨ p4)) := by
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_15 := assump_2 assump_66
      apply False.elim assump_15
    cases assump_6
    case intro assump_19 assump_20 =>
      have assump_67 : ((p6 ∧ False) ∨ (True ∨ p4)) := by
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_27 := assump_2 assump_67
      apply False.elim assump_27
  case inr assump_3 =>
    cases assump_3
    case intro assump_31 assump_32 =>
      cases assump_32
      case intro assump_35 assump_36 =>
        apply Or.inl
        apply Or.inl
        intro assump_41
        apply And.intro
        cases assump_41
        case intro assump_42 assump_43 =>
          have assump_68 : p4 := by
            exact assump_43
          let assump_52 := assump_35 assump_68
          apply False.elim assump_52
        cases assump_41
        case intro assump_56 assump_57 =>
          have assump_69 : p4 := by
            exact assump_57
          let assump_64 := assump_36 assump_69
          exact assump_64


variable (p0 p4 p3 p7 p1 p6 p5 p2 : Prop)
theorem file8_26087 : (((((p7 → p6) → (p2 → False)) ∨ ((p3 ∧ p5) → (True → p7))) ∨ (((True → p6) ∨ (p4 ∧ True)) → False)) → ((((p5 ∧ p4) → False) → ((p2 → p4) → False)) → (((False → p5) ∨ (p1 ∨ p2)) → ((p0 ∨ p1) → (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p2 p3 p0 p6 p1 : Prop)
theorem file8_26475 : (((((True ∨ p3) ∨ (p6 → False)) ∨ ((p1 → False) ∨ (p2 ∧ p0))) → False) → False) := by
  intro assump_1
  have assump_8 : (((True ∨ p3) ∨ (p6 → False)) ∨ ((p1 → False) ∨ (p2 ∧ p0))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p3 p4 p6 p7 p2 : Prop)
theorem file8_26858 : (((((p1 ∧ p6) ∧ (p2 ∧ p4)) → ((p7 → p7) → False)) → False) → ((((True → False) → (p6 ∨ p3)) ∨ ((p4 → True) → False)) ∨ (((p2 → p3) → False) ∨ ((True ∨ False) ∨ (p4 → p3))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p4 p2 p7 p1 : Prop)
theorem file8_27272 : ((((((p7 → False) ∧ (True → False)) ∨ ((p7 ∨ p2) ∧ (p7 ∧ p1))) → (((p2 ∧ p4) ∧ (True ∧ False)) → ((p4 → p4) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p7 → False) ∧ (True → False)) ∨ ((p7 ∨ p2) ∧ (p7 ∧ p1))) → (((p2 ∧ p4) ∧ (True ∧ False)) → ((p4 → p4) ∨ (True → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p5 p4 p0 p3 p7 p2 p6 p1 : Prop)
theorem file8_27978 : (((((p4 → p0) → (p6 ∨ True)) ∧ ((p0 ∨ p1) ∨ (p1 → p5))) ∧ (((False → False) ∨ (p3 ∧ p6)) → False)) → ((((p7 → False) ∧ (p7 ∨ p2)) ∧ ((p5 → False) ∨ (p2 → True))) ∨ (((p3 → False) ∧ (p0 ∨ True)) → ((p3 ∧ p2) → (True → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inr
          intro assump_27
          intro assump_28
          intro assump_29
          cases assump_28
          case intro assump_32 assump_33 =>
            cases assump_27
            case intro assump_38 assump_39 =>
              cases assump_39
              case inl assump_42 =>
                have assump_147 : p3 := by
                  exact assump_32
                let assump_47 := assump_38 assump_147
                apply False.elim assump_47
              case inr assump_43 =>
                have assump_148 : p3 := by
                  exact assump_32
                let assump_53 := assump_38 assump_148
                apply False.elim assump_53
        case inr assump_11 =>
          apply Or.inr
          intro assump_72
          intro assump_73
          intro assump_74
          cases assump_73
          case intro assump_77 assump_78 =>
            cases assump_72
            case intro assump_83 assump_84 =>
              cases assump_84
              case inl assump_87 =>
                have assump_149 : p3 := by
                  exact assump_77
                let assump_92 := assump_83 assump_149
                apply False.elim assump_92
              case inr assump_88 =>
                have assump_150 : p3 := by
                  exact assump_77
                let assump_98 := assump_83 assump_150
                apply False.elim assump_98
      case inr assump_9 =>
        apply Or.inr
        intro assump_117
        intro assump_118
        intro assump_119
        cases assump_118
        case intro assump_122 assump_123 =>
          cases assump_117
          case intro assump_128 assump_129 =>
            cases assump_129
            case inl assump_132 =>
              have assump_151 : p3 := by
                exact assump_122
              let assump_137 := assump_128 assump_151
              apply False.elim assump_137
            case inr assump_133 =>
              have assump_152 : p3 := by
                exact assump_122
              let assump_143 := assump_128 assump_152
              apply False.elim assump_143


variable (p4 p7 p5 p0 p1 p2 : Prop)
theorem file8_30620 : ((((((p5 ∧ False) → (p5 ∧ p0)) → ((p4 ∨ True) → False)) → (((p1 ∨ p5) ∨ (p5 → False)) ∨ ((p5 → p7) ∨ (p5 ∨ p2)))) → False) → False) := by
  intro assump_27
  have assump_59 : ((((p5 ∧ False) → (p5 ∧ p0)) → ((p4 ∨ True) → False)) → (((p1 ∨ p5) ∨ (p5 → False)) ∨ ((p5 → p7) ∨ (p5 ∨ p2)))) := by
    intro assump_31
    apply Or.inl
    apply Or.inr
    intro assump_34
    have assump_60 : ((p5 ∧ False) → (p5 ∧ p0)) := by
      intro assump_39
      apply And.intro
      cases assump_39
      case intro assump_40 assump_41 =>
        apply False.elim assump_41
      cases assump_39
      case intro assump_46 assump_47 =>
        apply False.elim assump_47
    let assump_38 := assump_31 assump_60
    have assump_61 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_52 := assump_38 assump_61
    apply False.elim assump_52
  let assump_30 := assump_27 assump_59
  apply False.elim assump_30


variable (p2 p0 p4 p1 p6 p7 : Prop)
theorem file8_31601 : ((((((False → False) → (False → False)) → ((p0 → False) → False)) → False) ∧ ((((p1 ∨ p2) ∧ (False ∧ p7)) ∧ ((p6 ∧ p6) → False)) ∧ (((True ∧ p4) ∧ (p7 → False)) → False))) → False) := by
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
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
          case inr assump_13 =>
            cases assump_11
            case intro assump_22 assump_23 =>
              apply False.elim assump_22


variable (p2 p7 p1 p4 p5 p6 : Prop)
theorem file8_32415 : (((((p6 ∨ p4) ∨ (p2 ∧ True)) ∧ ((p4 → False) → False)) → (((p7 ∧ False) ∨ (p5 ∧ p2)) → ((True → False) → (p6 ∨ p5)))) ∨ ((((True → False) → False) ∧ ((p1 ∨ p2) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  case inr assump_7 =>
    cases assump_7
    case intro assump_14 assump_15 =>
      cases assump_1
      case intro assump_20 assump_21 =>
        cases assump_20
        case inl assump_22 =>
          cases assump_22
          case inl assump_24 =>
            apply Or.inl
            exact assump_24
          case inr assump_25 =>
            apply Or.inr
            exact assump_14
        case inr assump_23 =>
          cases assump_23
          case intro assump_34 assump_35 =>
            apply Or.inr
            exact assump_14


variable (p4 p5 p7 : Prop)
theorem file8_33389 : ((((((p5 → p5) → False) ∧ ((p7 ∨ p4) ∧ (True → p7))) → False) → False) → False) := by
  intro assump_1
  have assump_45 : ((((p5 → p5) → False) ∧ ((p7 ∨ p4) ∧ (True → p7))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_46 : (p5 → p5) := by
            intro assump_22
            exact assump_22
          let assump_21 := assump_6 assump_46
          apply False.elim assump_21
        case inr assump_13 =>
          have assump_47 : (p5 → p5) := by
            intro assump_36
            exact assump_36
          let assump_35 := assump_6 assump_47
          apply False.elim assump_35
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


variable (p7 p6 p4 p5 p2 : Prop)
theorem file8_34282 : ((((((False → p6) ∧ (False ∨ p4)) ∨ ((p4 ∧ False) → False)) ∨ (((p2 → False) → False) → ((p5 ∨ p6) ∧ (p7 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → p6) ∧ (False ∨ p4)) ∨ ((p4 ∧ False) → False)) ∨ (((p2 → False) → False) → ((p5 ∨ p6) ∧ (p7 ∧ p2)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p1 p2 p0 p4 p6 : Prop)
theorem file8_34841 : (((((p4 ∨ False) ∨ (p2 ∧ p2)) → False) ∧ (((False ∨ True) ∨ (True ∧ p4)) → False)) → ((((p6 ∨ p1) ∨ (p0 ∧ p0)) ∨ ((p1 ∧ p5) ∨ (False → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_1
        case intro assump_11 assump_12 =>
          have assump_79 : ((False ∨ True) ∨ (True ∧ p4)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_17 := assump_12 assump_79
          apply False.elim assump_17
      case inr assump_8 =>
        cases assump_1
        case intro assump_23 assump_24 =>
          have assump_80 : ((False ∨ True) ∨ (True ∧ p4)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_29 := assump_24 assump_80
          apply False.elim assump_29
    case inr assump_6 =>
      cases assump_6
      case intro assump_33 assump_34 =>
        cases assump_1
        case intro assump_39 assump_40 =>
          have assump_81 : ((False ∨ True) ∨ (True ∧ p4)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_45 := assump_40 assump_81
          apply False.elim assump_45
  case inr assump_4 =>
    cases assump_4
    case inl assump_49 =>
      cases assump_49
      case intro assump_51 assump_52 =>
        cases assump_1
        case intro assump_57 assump_58 =>
          have assump_82 : ((False ∨ True) ∨ (True ∧ p4)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_63 := assump_58 assump_82
          apply False.elim assump_63
    case inr assump_50 =>
      cases assump_1
      case intro assump_69 assump_70 =>
        have assump_83 : ((False ∨ True) ∨ (True ∧ p4)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_75 := assump_70 assump_83
        apply False.elim assump_75


variable (p5 p0 p1 p6 p3 p7 p4 : Prop)
theorem file8_36943 : (((((p3 ∨ p0) → False) ∨ ((False → False) → False)) ∧ (((True → p0) ∨ (p1 ∧ p7)) ∧ ((p7 → True) → False))) → ((((p4 ∨ True) → (p1 ∧ p1)) → ((False → False) ∧ (p1 → False))) → (((p5 ∧ p7) → False) → ((False ∨ p6) ∧ (p6 ∨ False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_9
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          have assump_132 : (p7 → True) := by
            intro assump_23
            apply True.intro
          let assump_22 := assump_15 assump_132
          apply False.elim assump_22
        case inr assump_17 =>
          cases assump_17
          case intro assump_27 assump_28 =>
            have assump_133 : (p7 → True) := by
              intro assump_36
              apply True.intro
            let assump_35 := assump_15 assump_133
            apply False.elim assump_35
    case inr assump_11 =>
      cases assump_9
      case intro assump_42 assump_43 =>
        cases assump_42
        case inl assump_44 =>
          have assump_134 : (p7 → True) := by
            intro assump_51
            apply True.intro
          let assump_50 := assump_43 assump_134
          apply False.elim assump_50
        case inr assump_45 =>
          cases assump_45
          case intro assump_55 assump_56 =>
            have assump_135 : (p7 → True) := by
              intro assump_64
              apply True.intro
            let assump_63 := assump_43 assump_135
            apply False.elim assump_63
  cases assump_1
  case intro assump_72 assump_73 =>
    cases assump_72
    case inl assump_74 =>
      cases assump_73
      case intro assump_78 assump_79 =>
        cases assump_78
        case inl assump_80 =>
          have assump_136 : (p7 → True) := by
            intro assump_87
            apply True.intro
          let assump_86 := assump_79 assump_136
          apply False.elim assump_86
        case inr assump_81 =>
          cases assump_81
          case intro assump_91 assump_92 =>
            have assump_137 : (p7 → True) := by
              intro assump_100
              apply True.intro
            let assump_99 := assump_79 assump_137
            apply False.elim assump_99
    case inr assump_75 =>
      cases assump_73
      case intro assump_106 assump_107 =>
        cases assump_106
        case inl assump_108 =>
          have assump_138 : (p7 → True) := by
            intro assump_115
            apply True.intro
          let assump_114 := assump_107 assump_138
          apply False.elim assump_114
        case inr assump_109 =>
          cases assump_109
          case intro assump_119 assump_120 =>
            have assump_139 : (p7 → True) := by
              intro assump_128
              apply True.intro
            let assump_127 := assump_107 assump_139
            apply False.elim assump_127


variable (p2 p6 p1 p5 p7 p4 p0 p3 : Prop)
theorem file8_39985 : (((((p7 → True) ∨ (p1 ∧ p4)) → ((p6 ∧ p3) ∨ (p1 → False))) → (((p3 ∧ p7) ∨ (p0 → False)) → ((False ∧ p0) → (p7 ∨ p5)))) ∨ ((((False ∧ False) → (p3 → p0)) ∨ ((True ∨ p2) ∧ (False → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4


variable (p7 p5 p4 p2 p3 p1 : Prop)
theorem file8_40394 : (((((p5 ∨ p2) ∨ (p4 ∨ True)) ∨ ((p3 ∧ p4) → False)) ∨ (((p3 ∧ True) ∨ (False → p7)) ∨ ((p1 ∨ p2) ∨ (p3 → p2)))) ∨ ((((p4 ∨ True) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p4 p1 p7 : Prop)
theorem file8_40702 : ((((((p4 → False) ∧ (True ∧ p4)) ∧ ((p7 → False) ∨ (p1 → False))) → False) → False) → False) := by
  intro assump_11
  have assump_49 : ((((p4 → False) ∧ (True ∧ p4)) ∧ ((p7 → False) ∨ (p1 → False))) → False) := by
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_19
        case intro assump_22 assump_23 =>
          cases assump_17
          case inl assump_28 =>
            have assump_50 : p4 := by
              exact assump_23
            let assump_34 := assump_18 assump_50
            apply False.elim assump_34
          case inr assump_29 =>
            have assump_51 : p4 := by
              exact assump_23
            let assump_42 := assump_18 assump_51
            apply False.elim assump_42
  let assump_14 := assump_11 assump_49
  apply False.elim assump_14


variable (p3 p5 p0 p2 p6 p7 p4 : Prop)
theorem file8_41656 : (((((True ∧ p6) ∧ (p5 → False)) ∧ ((p0 → p6) → False)) ∧ (((p6 ∨ p6) ∨ (p2 ∧ p3)) → ((p7 ∨ True) → (p3 → False)))) → ((((p0 → p0) ∧ (p2 ∧ p3)) ∧ ((False ∨ p7) ∧ (p4 ∧ p2))) → False)) := by
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
          cases assump_15
          case inl assump_17 =>
            apply False.elim assump_17
          case inr assump_18 =>
            cases assump_16
            case intro assump_23 assump_24 =>
              cases assump_1
              case intro assump_29 assump_30 =>
                cases assump_29
                case intro assump_31 assump_32 =>
                  cases assump_31
                  case intro assump_33 assump_34 =>
                    cases assump_33
                    case intro assump_35 assump_36 =>
                      have assump_53 : ((p6 ∨ p6) ∨ (p2 ∧ p3)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_36
                      let assump_47 := assump_30 assump_53
                      have assump_54 : (p7 ∨ True) := by
                        apply Or.inl
                        exact assump_18
                      let assump_48 := assump_47 assump_54
                      have assump_55 : p3 := by
                        exact assump_10
                      let assump_49 := assump_48 assump_55
                      apply False.elim assump_49


variable (p1 p7 p2 p0 p3 p4 : Prop)
theorem file8_43339 : (((((p3 ∧ p7) ∨ (False → False)) → False) ∨ (((p1 ∧ p0) ∧ (p3 ∨ p3)) ∧ ((p4 ∨ p0) → False))) → ((((p7 → False) → (p1 → False)) → False) → (((p7 → False) ∧ (p2 ∨ p3)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      cases assump_1
      case inl assump_14 =>
        have assump_96 : ((p3 ∧ p7) ∨ (False → False)) := by
          apply Or.inr
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_14 assump_96
        apply False.elim assump_18
      case inr assump_15 =>
        cases assump_15
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            cases assump_27
            case intro assump_29 assump_30 =>
              cases assump_28
              case inl assump_35 =>
                have assump_97 : (p4 ∨ p0) := by
                  apply Or.inr
                  exact assump_30
                let assump_41 := assump_26 assump_97
                apply False.elim assump_41
              case inr assump_36 =>
                have assump_98 : (p4 ∨ p0) := by
                  apply Or.inr
                  exact assump_30
                let assump_49 := assump_26 assump_98
                apply False.elim assump_49
    case inr assump_9 =>
      cases assump_1
      case inl assump_57 =>
        have assump_99 : ((p3 ∧ p7) ∨ (False → False)) := by
          apply Or.inr
          intro assump_62
          apply False.elim assump_62
        let assump_61 := assump_57 assump_99
        apply False.elim assump_61
      case inr assump_58 =>
        cases assump_58
        case intro assump_68 assump_69 =>
          cases assump_68
          case intro assump_70 assump_71 =>
            cases assump_70
            case intro assump_72 assump_73 =>
              cases assump_71
              case inl assump_78 =>
                have assump_100 : (p4 ∨ p0) := by
                  apply Or.inr
                  exact assump_73
                let assump_84 := assump_69 assump_100
                apply False.elim assump_84
              case inr assump_79 =>
                have assump_101 : (p4 ∨ p0) := by
                  apply Or.inr
                  exact assump_73
                let assump_92 := assump_69 assump_101
                apply False.elim assump_92


variable (p4 p7 p2 p0 p1 p5 p3 p6 : Prop)
theorem file8_45835 : (((((p3 ∧ p2) ∧ (p4 ∧ p3)) ∧ ((p6 → False) ∨ (p1 ∧ p6))) → (((p7 → p0) → (p2 → False)) → ((p5 ∨ p2) → (p5 → False)))) → ((((p1 → True) ∨ (p1 → p7)) → ((False ∨ p2) → (p2 ∨ p0))) ∨ (((p6 → p4) ∧ (p3 ∨ p0)) ∧ ((p7 → True) → (False ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    apply False.elim assump_6
  case inr assump_7 =>
    cases assump_4
    case inl assump_12 =>
      apply Or.inl
      exact assump_7
    case inr assump_13 =>
      apply Or.inl
      exact assump_7


variable (p6 p5 p7 p4 p3 p2 p1 p0 : Prop)
theorem file8_46456 : (((((False → p6) → False) ∧ ((p4 ∨ p5) → False)) → False) ∨ ((((False → False) → False) → ((p1 ∧ p7) → (p2 → p7))) ∧ (((p3 → p2) ∧ (p2 ∨ p7)) ∧ ((p0 ∨ p6) → (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (False → p6) := by
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p7 p2 p6 p5 p1 p3 p0 : Prop)
theorem file8_46946 : (((((p2 ∨ p1) ∧ (True → False)) → False) → False) → ((((p3 → p3) ∧ (p0 → False)) ∧ ((p0 → False) ∨ (p6 ∨ p7))) ∧ (((True ∧ p1) ∧ (p7 ∧ p0)) ∨ ((p5 → False) → (p2 ∧ p2))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  exact assump_2
  intro assump_7
  have assump_127 : (((p2 ∨ p1) ∧ (True → False)) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        have assump_128 : True := by
          apply True.intro
        let assump_22 := assump_15 assump_128
        apply False.elim assump_22
      case inr assump_17 =>
        have assump_129 : True := by
          apply True.intro
        let assump_30 := assump_15 assump_129
        apply False.elim assump_30
  let assump_12 := assump_1 assump_127
  apply False.elim assump_12
  apply Or.inl
  intro assump_39
  have assump_130 : (((p2 ∨ p1) ∧ (True → False)) → False) := by
    intro assump_44
    cases assump_44
    case intro assump_45 assump_46 =>
      cases assump_45
      case inl assump_47 =>
        have assump_131 : True := by
          apply True.intro
        let assump_53 := assump_46 assump_131
        apply False.elim assump_53
      case inr assump_48 =>
        have assump_132 : True := by
          apply True.intro
        let assump_61 := assump_46 assump_132
        apply False.elim assump_61
  let assump_43 := assump_1 assump_130
  apply False.elim assump_43
  apply Or.inr
  intro assump_70
  apply And.intro
  have assump_133 : (((p2 ∨ p1) ∧ (True → False)) → False) := by
    intro assump_75
    cases assump_75
    case intro assump_76 assump_77 =>
      cases assump_76
      case inl assump_78 =>
        have assump_134 : True := by
          apply True.intro
        let assump_84 := assump_77 assump_134
        apply False.elim assump_84
      case inr assump_79 =>
        have assump_135 : True := by
          apply True.intro
        let assump_92 := assump_77 assump_135
        apply False.elim assump_92
  let assump_74 := assump_1 assump_133
  apply False.elim assump_74
  have assump_136 : (((p2 ∨ p1) ∧ (True → False)) → False) := by
    intro assump_103
    cases assump_103
    case intro assump_104 assump_105 =>
      cases assump_104
      case inl assump_106 =>
        have assump_137 : True := by
          apply True.intro
        let assump_112 := assump_105 assump_137
        apply False.elim assump_112
      case inr assump_107 =>
        have assump_138 : True := by
          apply True.intro
        let assump_120 := assump_105 assump_138
        apply False.elim assump_120
  let assump_102 := assump_1 assump_136
  apply False.elim assump_102


variable (p6 p0 p1 p2 p7 p3 : Prop)
theorem file8_49721 : (((((p6 ∨ p1) → False) → False) → (((p6 → False) → False) ∨ ((p7 → p2) ∧ (True → False)))) → ((((False ∨ True) → False) → False) ∨ (((p3 ∧ p0) → (p3 ∨ p1)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_11 : (False ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p1 p6 p2 p7 p5 p4 p3 : Prop)
theorem file8_50149 : (((((p3 ∧ p3) → False) → False) → False) → ((((p7 ∨ p7) → False) → ((False ∧ p6) → (p4 → p4))) ∨ (((p6 ∧ p1) ∧ (p4 → p5)) ∨ ((p4 ∨ p7) ∨ (p2 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    apply False.elim assump_9


variable (p1 p7 p0 p4 p2 p3 : Prop)
theorem file8_50534 : (((((p3 ∧ p7) → False) ∧ ((p4 ∧ p7) ∨ (p7 ∧ p1))) → (((p0 ∨ p2) → False) → ((False → False) ∧ (p3 → p3)))) ∨ ((((True ∧ p0) ∨ (True → False)) → ((p1 ∨ True) → False)) ∨ (((True → p3) ∧ (p1 → True)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  cases assump_1
  case intro assump_11 assump_12 =>
    cases assump_12
    case inl assump_15 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        exact assump_6
    case inr assump_16 =>
      cases assump_16
      case intro assump_23 assump_24 =>
        exact assump_6


variable (p6 p4 p5 p3 p1 p7 p2 : Prop)
theorem file8_51236 : (((((p5 ∧ p1) → (False → False)) → False) → (((p4 ∨ p3) → False) → False)) ∨ ((((False ∨ True) → (p7 → False)) → ((p2 ∧ p6) → (p2 → False))) → (((p2 ∧ p3) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_15 : ((p5 ∧ p1) → (False → False)) := by
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_7 := assump_1 assump_15
  apply False.elim assump_7


variable (p5 p1 p3 p4 p7 p2 p6 : Prop)
theorem file8_51717 : (((((True → True) → (p7 → False)) ∧ ((False ∧ p1) ∨ (False → False))) ∨ (((p4 ∧ p6) ∧ (p2 ∧ p6)) ∧ ((True → p3) → False))) → ((((True → False) → False) → False) → (((p7 ∨ p5) ∨ (p1 ∧ p6)) ∨ ((p6 → False) → (True ∧ p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
      case inr assump_12 =>
        apply Or.inr
        intro assump_19
        apply And.intro
        apply True.intro
        have assump_59 : ((True → False) → False) := by
          intro assump_28
          have assump_60 : True := by
            apply True.intro
          let assump_31 := assump_28 assump_60
          apply False.elim assump_31
        let assump_27 := assump_2 assump_59
        apply False.elim assump_27
  case inr assump_6 =>
    cases assump_6
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          cases assump_41
          case intro assump_48 assump_49 =>
            apply Or.inr
            intro assump_56
            apply And.intro
            apply True.intro
            exact assump_42


variable (p2 p3 p4 p7 p1 : Prop)
theorem file8_53133 : (((((p2 → False) ∨ (p1 ∧ p2)) → ((p3 → False) → (p7 → False))) ∧ (((p1 ∧ False) → (p2 ∨ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p1 ∧ False) → (p2 ∨ p4)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p1 p7 p4 p0 p5 : Prop)
theorem file8_53616 : (((((p5 ∧ False) → (p5 ∧ True)) → False) → False) ∨ ((((True → False) ∧ (p1 ∧ p5)) ∨ ((p7 ∨ p4) → (True → p0))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p5 ∧ False) → (p5 ∧ True)) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
    apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p4 p5 p0 p6 p1 p7 p2 : Prop)
theorem file8_54108 : (((((p6 ∧ False) → (p7 ∧ p3)) → ((p1 → False) ∧ (p5 → False))) → False) → ((((p2 → False) ∧ (False ∨ False)) → ((p4 ∨ p7) → False)) ∨ (((True ∧ p2) ∧ (True ∧ p5)) ∨ ((p0 → False) ∧ (p0 ∧ True))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_4
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        apply False.elim assump_14
      case inr assump_15 =>
        apply False.elim assump_15
  case inr assump_7 =>
    cases assump_4
    case intro assump_22 assump_23 =>
      cases assump_23
      case inl assump_26 =>
        apply False.elim assump_26
      case inr assump_27 =>
        apply False.elim assump_27


variable (p6 p3 p4 p7 p0 p1 : Prop)
theorem file8_54910 : (((((True ∨ p6) → (p3 ∨ p1)) → ((p6 → p4) → False)) ∧ (((p1 ∨ True) ∧ (p6 → False)) ∧ ((p7 → p0) ∧ (p1 ∧ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              have assump_54 : p6 := by
                exact assump_21
              let assump_29 := assump_9 assump_54
              apply False.elim assump_29
        case inr assump_11 =>
          cases assump_7
          case intro assump_37 assump_38 =>
            cases assump_38
            case intro assump_41 assump_42 =>
              have assump_55 : p6 := by
                exact assump_42
              let assump_50 := assump_9 assump_55
              apply False.elim assump_50


variable (p5 p6 p7 p2 p3 p0 : Prop)
theorem file8_55974 : (((((p5 ∨ False) ∧ (False ∧ p3)) ∨ ((False ∧ p2) → False)) ∧ (((p6 → False) ∧ (False → p0)) → ((p6 → False) ∧ (p5 ∨ True)))) ∨ ((((p2 ∨ p7) → (False → False)) ∨ ((p3 → p2) → (p2 ∧ p3))) ∨ (((p3 → p7) → (p5 ∨ False)) → False))) := by
  apply Or.inl
  apply And.intro
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2
  intro assump_6
  apply And.intro
  intro assump_7
  cases assump_6
  case intro assump_10 assump_11 =>
    have assump_27 : p6 := by
      exact assump_7
    let assump_17 := assump_10 assump_27
    apply False.elim assump_17
  cases assump_6
  case intro assump_21 assump_22 =>
    apply Or.inr
    apply True.intro


variable (p6 p0 p5 p1 p3 p2 p7 p4 : Prop)
theorem file8_56738 : (((((p3 ∧ p2) ∧ (p5 → False)) → ((p1 ∧ True) ∨ (True → p0))) → False) → ((((p2 → False) ∧ (p0 → p7)) → False) ∨ (((p6 ∧ p7) → (p4 → p2)) → False))) := by
  intro assump_32
  apply Or.inl
  intro assump_35
  cases assump_35
  case intro assump_36 assump_37 =>
    have assump_70 : (((p3 ∧ p2) ∧ (p5 → False)) → ((p1 ∧ True) ∨ (True → p0))) := by
      intro assump_45
      cases assump_45
      case intro assump_46 assump_47 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          apply Or.inr
          intro assump_56
          have assump_71 : p2 := by
            exact assump_49
          let assump_63 := assump_36 assump_71
          apply False.elim assump_63
    let assump_44 := assump_32 assump_70
    apply False.elim assump_44


variable (p7 p1 p6 p5 p2 p4 p0 : Prop)
theorem file8_57565 : ((((((p5 → False) ∧ (False ∨ True)) → ((p1 ∨ p1) ∨ (p2 ∧ p6))) ∧ (((p5 → True) → (True ∨ False)) → False)) ∧ ((((p4 ∧ p4) ∧ (p5 ∨ p7)) ∨ ((p4 ∧ p5) → (True → False))) ∧ (((p0 ∨ p2) ∧ (True → p4)) → ((p7 ∨ False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_15
              case inl assump_22 =>
                have assump_67 : ((p5 → True) → (True ∨ False)) := by
                  intro assump_33
                  apply Or.inl
                  apply True.intro
                let assump_32 := assump_5 assump_67
                apply False.elim assump_32
              case inr assump_23 =>
                have assump_68 : ((p5 → True) → (True ∨ False)) := by
                  intro assump_48
                  apply Or.inl
                  apply True.intro
                let assump_47 := assump_5 assump_68
                apply False.elim assump_47
        case inr assump_13 =>
          have assump_69 : ((p5 → True) → (True ∨ False)) := by
            intro assump_61
            apply Or.inl
            apply True.intro
          let assump_60 := assump_5 assump_69
          apply False.elim assump_60


variable (p1 p2 p6 p4 p7 p0 p3 : Prop)
theorem file8_59140 : ((((((False → p6) → False) → ((p2 → False) → (p0 → False))) ∨ (((p7 ∧ False) ∨ (p2 → p2)) ∨ ((p3 → False) → (p7 → p1)))) ∧ ((((False ∧ p3) → (p6 → False)) ∨ ((p4 → False) → (True → False))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      have assump_68 : (((False ∧ p3) → (p6 → False)) ∨ ((p4 → False) → (True → False))) := by
        apply Or.inl
        intro assump_15
        intro assump_16
        cases assump_15
        case intro assump_19 assump_20 =>
          apply False.elim assump_19
      let assump_14 := assump_7 assump_68
      apply False.elim assump_14
    case inr assump_9 =>
      cases assump_9
      case inl assump_26 =>
        cases assump_26
        case inl assump_28 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            apply False.elim assump_31
        case inr assump_29 =>
          have assump_69 : (((False ∧ p3) → (p6 → False)) ∨ ((p4 → False) → (True → False))) := by
            apply Or.inl
            intro assump_41
            intro assump_42
            cases assump_41
            case intro assump_45 assump_46 =>
              apply False.elim assump_45
          let assump_40 := assump_7 assump_69
          apply False.elim assump_40
      case inr assump_27 =>
        have assump_70 : (((False ∧ p3) → (p6 → False)) ∨ ((p4 → False) → (True → False))) := by
          apply Or.inl
          intro assump_57
          intro assump_58
          cases assump_57
          case intro assump_61 assump_62 =>
            apply False.elim assump_61
        let assump_56 := assump_7 assump_70
        apply False.elim assump_56


variable (p3 p4 p0 p5 p6 p1 : Prop)
theorem file8_60902 : ((((((p1 ∧ True) → False) → ((True → False) ∧ (p6 → False))) ∨ (((p3 ∧ p4) → (False ∨ False)) ∨ ((p5 → False) ∨ (p1 → False)))) ∧ ((((p6 ∧ p6) ∨ (False ∨ p0)) → ((False → False) → (p1 ∨ True))) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      have assump_120 : (((p6 ∧ p6) ∨ (False ∨ p0)) → ((False → False) → (p1 ∨ True))) := by
        intro assump_17
        intro assump_18
        cases assump_17
        case inl assump_21 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            apply Or.inr
            apply True.intro
        case inr assump_22 =>
          cases assump_22
          case inl assump_29 =>
            apply False.elim assump_29
          case inr assump_30 =>
            apply Or.inr
            apply True.intro
      let assump_16 := assump_9 assump_120
      apply False.elim assump_16
    case inr assump_11 =>
      cases assump_11
      case inl assump_38 =>
        have assump_121 : (((p6 ∧ p6) ∨ (False ∨ p0)) → ((False → False) → (p1 ∨ True))) := by
          intro assump_45
          intro assump_46
          cases assump_45
          case inl assump_49 =>
            cases assump_49
            case intro assump_51 assump_52 =>
              apply Or.inr
              apply True.intro
          case inr assump_50 =>
            cases assump_50
            case inl assump_57 =>
              apply False.elim assump_57
            case inr assump_58 =>
              apply Or.inr
              apply True.intro
        let assump_44 := assump_9 assump_121
        apply False.elim assump_44
      case inr assump_39 =>
        cases assump_39
        case inl assump_66 =>
          have assump_122 : (((p6 ∧ p6) ∨ (False ∨ p0)) → ((False → False) → (p1 ∨ True))) := by
            intro assump_73
            intro assump_74
            cases assump_73
            case inl assump_77 =>
              cases assump_77
              case intro assump_79 assump_80 =>
                apply Or.inr
                apply True.intro
            case inr assump_78 =>
              cases assump_78
              case inl assump_85 =>
                apply False.elim assump_85
              case inr assump_86 =>
                apply Or.inr
                apply True.intro
          let assump_72 := assump_9 assump_122
          apply False.elim assump_72
        case inr assump_67 =>
          have assump_123 : (((p6 ∧ p6) ∨ (False ∨ p0)) → ((False → False) → (p1 ∨ True))) := by
            intro assump_99
            intro assump_100
            cases assump_99
            case inl assump_103 =>
              cases assump_103
              case intro assump_105 assump_106 =>
                apply Or.inr
                apply True.intro
            case inr assump_104 =>
              cases assump_104
              case inl assump_111 =>
                apply False.elim assump_111
              case inr assump_112 =>
                apply Or.inr
                apply True.intro
          let assump_98 := assump_9 assump_123
          apply False.elim assump_98


theorem file8_64068 : ((((((False ∧ True) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ True) → False) → False) → False) := by
    intro assump_5
    have assump_21 : ((False ∧ True) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p5 p1 p2 p3 p6 p4 p7 p0 : Prop)
theorem file8_64614 : (((((p2 ∧ p4) → (p5 → p4)) → ((False ∧ True) → False)) ∨ (((p5 → False) ∨ (True → False)) → False)) → ((((False → False) → False) → ((p6 → False) ∨ (p4 ∧ p4))) ∨ (((p4 → False) ∨ (p0 → p7)) → ((p3 ∨ p1) → False)))) := by
  intro assump_16
  cases assump_16
  case inl assump_17 =>
    apply Or.inl
    intro assump_21
    apply Or.inl
    intro assump_24
    have assump_51 : (False → False) := by
      intro assump_29
      apply False.elim assump_29
    let assump_28 := assump_21 assump_51
    apply False.elim assump_28
  case inr assump_18 =>
    apply Or.inl
    intro assump_37
    apply Or.inl
    intro assump_40
    have assump_52 : (False → False) := by
      intro assump_45
      apply False.elim assump_45
    let assump_44 := assump_37 assump_52
    apply False.elim assump_44


variable (p4 p3 p6 p7 p1 p2 p5 : Prop)
theorem file8_65470 : (((((p5 ∧ False) ∧ (p6 → p3)) → ((p7 ∨ p7) → (p5 → False))) → False) → ((((False ∨ True) ∧ (True → p2)) ∨ ((p4 → False) ∨ (p1 → p5))) ∨ (((p4 → p5) → False) → ((p5 ∧ p1) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inr
  apply True.intro
  intro assump_4
  have assump_38 : (((p5 ∧ False) ∧ (p6 → p3)) → ((p7 ∨ p7) → (p5 → False))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    cases assump_9
    case inl assump_13 =>
      cases assump_8
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          apply False.elim assump_20
    case inr assump_14 =>
      cases assump_8
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          apply False.elim assump_30
  let assump_7 := assump_1 assump_38
  apply False.elim assump_7


variable (p1 p3 p2 p6 p0 : Prop)
theorem file8_66436 : ((((((True ∨ p3) ∨ (p0 → False)) → False) → (((p0 → False) → (p2 ∨ p6)) → ((p1 ∧ p1) → (p2 → p0)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((True ∨ p3) ∨ (p0 → False)) → False) → (((p0 → False) → (p2 ∨ p6)) → ((p1 ∧ p1) → (p2 → p0)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      have assump_29 : ((True ∨ p3) ∨ (p0 → False)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_21 := assump_5 assump_29
      apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p6 p1 p7 p0 p5 p4 : Prop)
theorem file8_67158 : ((((((p4 → p6) ∧ (p7 ∧ p1)) → ((p7 ∨ True) ∨ (p0 → p1))) ∨ (((p0 → p4) → (p0 → False)) → ((True ∨ p0) ∨ (p5 → False)))) → False) → False) := by
  intro assump_5
  have assump_23 : ((((p4 → p6) ∧ (p7 ∧ p1)) → ((p7 ∨ True) ∨ (p0 → p1))) ∨ (((p0 → p4) → (p0 → False)) → ((True ∨ p0) ∨ (p5 → False)))) := by
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply Or.inl
        apply Or.inl
        exact assump_14
  let assump_8 := assump_5 assump_23
  apply False.elim assump_8


variable (p1 p0 : Prop)
theorem file8_67796 : (((((True → False) ∧ (True → p0)) → ((p0 → False) ∧ (False ∧ p1))) → False) → False) := by
  intro assump_1
  have assump_48 : (((True → False) ∧ (True → p0)) → ((p0 → False) ∧ (False ∧ p1))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_49 : True := by
        apply True.intro
      let assump_17 := assump_9 assump_49
      apply False.elim assump_17
    apply And.intro
    cases assump_5
    case intro assump_21 assump_22 =>
      have assump_50 : True := by
        apply True.intro
      let assump_29 := assump_21 assump_50
      apply False.elim assump_29
    cases assump_5
    case intro assump_33 assump_34 =>
      have assump_51 : True := by
        apply True.intro
      let assump_41 := assump_33 assump_51
      apply False.elim assump_41
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p6 p5 p3 p4 p7 : Prop)
theorem file8_68768 : (((((p7 ∧ p6) ∧ (False ∧ p4)) ∧ ((p3 → False) ∨ (p7 ∧ p5))) ∧ (((p7 ∨ p3) ∨ (False → False)) → False)) → False) := by
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
            apply False.elim assump_14


variable (p1 p5 : Prop)
theorem file8_69287 : (((((p1 → p5) → False) → ((p5 ∧ False) ∨ (False → False))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p1 → p5) → False) → ((p5 ∧ False) ∨ (False → False))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p2 p3 p6 p5 p0 p7 p4 : Prop)
theorem file8_69685 : (((((p5 ∨ True) ∧ (p7 → p2)) ∧ ((p0 ∧ p4) ∧ (p0 → False))) → False) ∧ ((((p5 ∧ p3) → (True → False)) ∧ ((p1 → p0) ∧ (p6 → True))) → (((False → False) → False) → False))) := by
  apply And.intro
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_12
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            have assump_77 : p0 := by
              exact assump_23
            let assump_31 := assump_22 assump_77
            apply False.elim assump_31
      case inr assump_16 =>
        cases assump_12
        case intro assump_39 assump_40 =>
          cases assump_39
          case intro assump_41 assump_42 =>
            have assump_78 : p0 := by
              exact assump_41
            let assump_49 := assump_40 assump_78
            apply False.elim assump_49
  intro assump_53
  intro assump_54
  cases assump_53
  case intro assump_57 assump_58 =>
    cases assump_58
    case intro assump_61 assump_62 =>
      have assump_79 : (False → False) := by
        intro assump_71
        apply False.elim assump_71
      let assump_70 := assump_54 assump_79
      apply False.elim assump_70


variable (p7 p2 p5 p3 : Prop)
theorem file8_71053 : ((((((True → False) ∧ (p2 → False)) ∧ ((p7 ∨ p3) ∨ (p5 ∧ False))) → False) → False) → False) := by
  intro assump_22
  have assump_64 : ((((True → False) ∧ (p2 → False)) ∧ ((p7 ∨ p3) ∨ (p5 ∧ False))) → False) := by
    intro assump_26
    cases assump_26
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_28
        case inl assump_35 =>
          cases assump_35
          case inl assump_37 =>
            have assump_65 : True := by
              apply True.intro
            let assump_43 := assump_29 assump_65
            apply False.elim assump_43
          case inr assump_38 =>
            have assump_66 : True := by
              apply True.intro
            let assump_51 := assump_29 assump_66
            apply False.elim assump_51
        case inr assump_36 =>
          cases assump_36
          case intro assump_55 assump_56 =>
            apply False.elim assump_56
  let assump_25 := assump_22 assump_64
  apply False.elim assump_25


variable (p7 p6 p4 p2 p0 p5 p3 : Prop)
theorem file8_72140 : (((((False → False) → False) → False) ∧ (((p2 → False) ∨ (p7 → p2)) → ((p3 ∨ p4) → False))) → ((((False ∧ p4) → (p6 ∨ p2)) ∨ ((p2 ∧ p7) ∧ (False → p7))) ∨ (((p5 ∧ False) → (p7 ∨ p3)) ∧ ((p2 ∧ p7) → (p7 ∧ p0))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9


variable (p6 p3 p2 p0 p5 p4 p1 : Prop)
theorem file8_72630 : (((((p0 ∨ True) ∧ (p3 ∧ p5)) ∧ ((p4 → False) ∨ (p1 ∨ p3))) → False) → ((((p2 ∨ p2) → False) ∧ ((False → p2) ∧ (p6 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12


variable (p2 p5 p7 p3 p4 p0 : Prop)
theorem file8_73067 : ((((((p4 → p4) ∨ (p5 ∨ p3)) → ((p0 ∧ p4) → (p3 → False))) → (((True → False) ∨ (p3 ∧ p7)) → False)) ∧ ((((p4 ∨ p5) → (p2 ∨ True)) ∨ ((True → False) ∧ (p4 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p4 ∨ p5) → (p2 ∨ True)) ∨ ((True → False) ∧ (p4 ∧ p2))) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inr
        apply True.intro
      case inr assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p6 p7 p5 : Prop)
theorem file8_73737 : (((((p7 → p6) ∨ (p7 → False)) → False) → False) → ((((p7 ∨ p5) ∨ (False → False)) ∧ ((p6 ∧ True) → (p7 → p7))) ∨ (((p7 → False) → False) ∨ ((True ∨ False) → (p7 ∨ p7))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  apply Or.inr
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    exact assump_8


variable (p4 p3 p1 p5 p6 p2 : Prop)
theorem file8_74190 : ((((((False ∧ p4) ∧ (p4 → p2)) → ((p4 ∧ p6) ∨ (True → False))) ∧ (((False → p1) ∧ (True → True)) → False)) ∨ ((((p3 ∧ False) → False) → ((True ∨ p5) ∨ (p6 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_27 : ((False → p1) ∧ (True → True)) := by
        apply And.intro
        intro assump_11
        apply False.elim assump_11
        intro assump_14
        apply True.intro
      let assump_10 := assump_5 assump_27
      apply False.elim assump_10
  case inr assump_3 =>
    have assump_28 : (((p3 ∧ False) → False) → ((True ∨ p5) ∨ (p6 ∨ p6))) := by
      intro assump_21
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_20 := assump_3 assump_28
    apply False.elim assump_20


variable (p1 p6 : Prop)
theorem file8_75062 : (((((False ∨ False) → False) ∨ ((False ∧ p6) ∨ (p1 → p1))) → False) → False) := by
  intro assump_1
  have assump_15 : (((False ∨ False) → False) ∨ ((False ∧ p6) ∨ (p1 → p1))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply False.elim assump_6
    case inr assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p1 p5 p6 p7 p4 p3 : Prop)
theorem file8_75541 : (((((False ∨ True) → False) ∧ ((p4 ∨ p3) → (p7 ∧ p5))) ∨ (((p3 ∧ p4) ∨ (p7 ∨ p2)) → ((False → False) → False))) → ((((p2 → p7) ∨ (p2 ∨ p7)) ∨ ((False → p2) ∧ (p1 ∧ p5))) ∨ (((p5 → p6) → (p2 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      intro assump_10
      have assump_33 : (False ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_15 := assump_4 assump_33
      apply False.elim assump_15
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_21
    have assump_34 : ((p3 ∧ p4) ∨ (p7 ∨ p2)) := by
      apply Or.inr
      apply Or.inr
      exact assump_21
    let assump_25 := assump_3 assump_34
    have assump_35 : (False → False) := by
      intro assump_27
      apply False.elim assump_27
    let assump_26 := assump_25 assump_35
    apply False.elim assump_26


variable (p4 p2 : Prop)
theorem file8_76577 : ((((((p4 → False) → False) ∧ ((False ∧ p2) ∧ (False → False))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p4 → False) → False) ∧ ((False ∧ p2) ∧ (False → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p3 p1 p5 p4 : Prop)
theorem file8_77142 : (((((p3 → False) → False) → ((p5 → False) → (p5 → False))) ∧ (((p4 ∨ True) ∨ (p4 ∧ p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((p4 ∨ True) ∨ (p4 ∧ p1)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p7 p1 p6 p2 p0 p4 p3 : Prop)
theorem file8_77569 : (((((p6 → True) ∨ (p4 → False)) ∧ ((p0 ∧ p1) ∧ (p7 ∨ p3))) → (((p4 → p1) → False) → ((p7 → p6) ∧ (p6 → False)))) → ((((p2 → p1) ∧ (p7 → p0)) → False) → (((p7 ∨ p6) ∨ (True → False)) → ((p7 ∧ False) ∨ (p7 → p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      apply Or.inr
      intro assump_14
      exact assump_14
    case inr assump_7 =>
      apply Or.inr
      intro assump_23
      exact assump_23
  case inr assump_5 =>
    apply Or.inr
    intro assump_32
    exact assump_32


variable (p5 p4 p6 p3 p2 p0 p1 p7 : Prop)
theorem file8_78221 : (((((p6 → p1) ∧ (False ∨ False)) → False) ∨ (((p1 ∨ p4) ∧ (p6 ∧ p6)) ∧ ((True → p1) → False))) ∨ ((((p5 ∨ p1) → (p5 ∨ p3)) → ((p5 → p7) ∨ (p0 ∨ p2))) ∨ (((p0 → True) → False) → ((False ∨ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply False.elim assump_6
    case inr assump_7 =>
      apply False.elim assump_7


variable (p3 p7 p5 p2 p6 p1 : Prop)
theorem file8_78723 : (((((p2 → p2) ∨ (True → p2)) → False) → (((True → p2) ∨ (p3 → False)) ∧ ((p5 → False) → False))) ∨ ((((p5 ∧ p2) → (p5 ∧ p2)) ∧ ((p1 ∧ False) ∨ (p2 → True))) ∨ (((p7 ∨ p5) ∧ (p5 ∨ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_26 : ((p2 → p2) ∨ (True → p2)) := by
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_7 := assump_1 assump_26
  apply False.elim assump_7
  intro assump_14
  have assump_27 : ((p2 → p2) ∨ (True → p2)) := by
    apply Or.inl
    intro assump_20
    exact assump_20
  let assump_19 := assump_1 assump_27
  apply False.elim assump_19


variable (p2 p6 p7 p4 p0 p1 : Prop)
theorem file8_79430 : (((((p7 ∨ True) → False) ∨ ((True ∨ p4) → False)) → (((p4 ∨ True) → (p6 ∧ p4)) ∨ ((True ∧ False) ∨ (p6 ∨ p2)))) ∨ ((((False ∧ p1) ∧ (p2 → p4)) → ((p0 → False) ∨ (True → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      have assump_60 : (p7 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_2 assump_60
      apply False.elim assump_12
    case inr assump_8 =>
      have assump_61 : (p7 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_18 := assump_2 assump_61
      apply False.elim assump_18
    cases assump_6
    case inl assump_22 =>
      exact assump_22
    case inr assump_23 =>
      have assump_62 : (p7 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_28 := assump_2 assump_62
      apply False.elim assump_28
  case inr assump_3 =>
    apply Or.inl
    intro assump_34
    apply And.intro
    cases assump_34
    case inl assump_35 =>
      have assump_63 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_40 := assump_3 assump_63
      apply False.elim assump_40
    case inr assump_36 =>
      have assump_64 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_46 := assump_3 assump_64
      apply False.elim assump_46
    cases assump_34
    case inl assump_50 =>
      exact assump_50
    case inr assump_51 =>
      have assump_65 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_56 := assump_3 assump_65
      apply False.elim assump_56


variable (p7 p6 p0 p4 p3 p1 p5 p2 : Prop)
theorem file8_81198 : ((((((True ∧ False) → (False ∧ p7)) → ((p5 ∨ p2) ∧ (p3 ∧ p6))) ∧ (((True → True) ∨ (p0 ∧ p5)) ∧ ((p7 → p5) ∨ (p4 → False)))) ∧ ((((False ∧ True) → False) ∨ ((p3 ∨ p6) ∧ (True → p1))) → False)) → False) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        cases assump_20
        case inl assump_22 =>
          cases assump_21
          case inl assump_26 =>
            have assump_88 : (((False ∧ True) → False) ∨ ((p3 ∨ p6) ∧ (True → p1))) := by
              apply Or.inl
              intro assump_33
              cases assump_33
              case intro assump_34 assump_35 =>
                apply False.elim assump_34
            let assump_32 := assump_15 assump_88
            apply False.elim assump_32
          case inr assump_27 =>
            have assump_89 : (((False ∧ True) → False) ∨ ((p3 ∨ p6) ∧ (True → p1))) := by
              apply Or.inl
              intro assump_46
              cases assump_46
              case intro assump_47 assump_48 =>
                apply False.elim assump_47
            let assump_45 := assump_15 assump_89
            apply False.elim assump_45
        case inr assump_23 =>
          cases assump_23
          case intro assump_54 assump_55 =>
            cases assump_21
            case inl assump_60 =>
              have assump_90 : (((False ∧ True) → False) ∨ ((p3 ∨ p6) ∧ (True → p1))) := by
                apply Or.inl
                intro assump_67
                cases assump_67
                case intro assump_68 assump_69 =>
                  apply False.elim assump_68
              let assump_66 := assump_15 assump_90
              apply False.elim assump_66
            case inr assump_61 =>
              have assump_91 : (((False ∧ True) → False) ∨ ((p3 ∨ p6) ∧ (True → p1))) := by
                apply Or.inl
                intro assump_80
                cases assump_80
                case intro assump_81 assump_82 =>
                  apply False.elim assump_81
              let assump_79 := assump_15 assump_91
              apply False.elim assump_79


variable (p0 p5 p3 p6 p2 p4 p7 : Prop)
theorem file8_83457 : (((((p5 ∨ p0) → (True → False)) → ((p4 ∧ p2) → (True ∨ p4))) → False) → ((((p0 ∧ p5) ∧ (p6 → p4)) → ((p2 → False) ∨ (False ∨ p7))) → (((p0 → False) → (p7 ∧ p7)) ∨ ((False → False) → (p7 ∧ p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply And.intro
  have assump_42 : (((p5 ∨ p0) → (True → False)) → ((p4 ∧ p2) → (True ∨ p4))) := by
    intro assump_12
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply Or.inl
      apply True.intro
  let assump_11 := assump_1 assump_42
  apply False.elim assump_11
  have assump_43 : (((p5 ∨ p0) → (True → False)) → ((p4 ∧ p2) → (True ∨ p4))) := by
    intro assump_29
    intro assump_30
    cases assump_30
    case intro assump_31 assump_32 =>
      apply Or.inl
      apply True.intro
  let assump_28 := assump_1 assump_43
  apply False.elim assump_28


variable (p2 p1 p3 : Prop)
theorem file8_84376 : ((((((p1 → p1) ∨ (p2 ∧ p3)) ∧ ((False → p2) → (True → False))) → False) → False) → False) := by
  intro assump_1
  have assump_41 : ((((p1 → p1) ∨ (p2 ∧ p3)) ∧ ((False → p2) → (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_42 : (False → p2) := by
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_7 assump_42
        have assump_43 : True := by
          apply True.intro
        let assump_18 := assump_14 assump_43
        apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case intro assump_22 assump_23 =>
          have assump_44 : (False → p2) := by
            intro assump_31
            apply False.elim assump_31
          let assump_30 := assump_7 assump_44
          have assump_45 : True := by
            apply True.intro
          let assump_34 := assump_30 assump_45
          apply False.elim assump_34
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p7 p5 p6 p3 p0 p1 p4 : Prop)
theorem file8_85530 : (((((p3 → False) → (False ∧ p0)) ∧ ((p5 → False) → False)) ∧ (((True ∧ p4) → (p6 ∨ False)) → ((True ∧ p3) ∨ (False → False)))) → ((((p6 ∨ p7) → (True ∨ p4)) ∨ ((p1 → p0) → False)) ∨ (((p7 ∧ p3) ∨ (p0 → p6)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      cases assump_12
      case inl assump_13 =>
        apply Or.inl
        apply True.intro
      case inr assump_14 =>
        apply Or.inl
        apply True.intro


variable (p0 p7 p2 p4 p5 p6 : Prop)
theorem file8_86167 : ((((((p6 ∧ p7) ∧ (p5 ∧ p6)) → ((p5 ∨ p4) ∧ (p5 ∨ p6))) ∨ (((p2 → False) → (p2 → False)) → ((p7 → True) ∧ (p0 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p6 ∧ p7) ∧ (p5 ∧ p6)) → ((p5 ∨ p4) ∧ (p5 ∨ p6))) ∨ (((p2 → False) → (p2 → False)) → ((p7 → True) ∧ (p0 ∨ True)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply Or.inl
          exact assump_14
    cases assump_5
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_21
        case intro assump_28 assump_29 =>
          apply Or.inl
          exact assump_28
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p1 p5 p6 p2 p7 p4 p3 : Prop)
theorem file8_87117 : (((((False ∨ p5) → (p5 ∧ True)) → False) → (((p6 ∨ p2) → (p2 → False)) ∨ ((p5 → p1) ∨ (False ∨ p7)))) ∨ ((((p4 → p5) ∧ (False ∧ p7)) → ((p3 ∧ p4) → False)) ∧ (((p3 ∧ p4) ∧ (p7 → False)) ∧ ((p7 ∧ p5) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_40 : ((False ∨ p5) → (p5 ∧ True)) := by
      intro assump_15
      apply And.intro
      cases assump_15
      case inl assump_16 =>
        apply False.elim assump_16
      case inr assump_17 =>
        exact assump_17
      apply True.intro
    let assump_14 := assump_1 assump_40
    apply False.elim assump_14
  case inr assump_9 =>
    have assump_41 : ((False ∨ p5) → (p5 ∧ True)) := by
      intro assump_30
      apply And.intro
      cases assump_30
      case inl assump_31 =>
        apply False.elim assump_31
      case inr assump_32 =>
        exact assump_32
      apply True.intro
    let assump_29 := assump_1 assump_41
    apply False.elim assump_29


variable (p7 p2 p6 p3 p4 p0 : Prop)
theorem file8_88200 : (((((False ∧ p4) ∧ (p7 → False)) → False) → False) → ((((p7 ∨ p3) ∨ (p3 ∨ p7)) ∧ ((p2 ∧ False) ∨ (p0 → False))) ∨ (((p2 ∧ p6) → (p7 ∧ p6)) ∧ ((p6 → False) ∨ (p7 → False))))) := by
  intro assump_1
  apply Or.inr
  apply And.intro
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_45 : (((False ∧ p4) ∧ (p7 → False)) → False) := by
      intro assump_14
      cases assump_14
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
    let assump_13 := assump_1 assump_45
    apply False.elim assump_13
  cases assump_4
  case intro assump_24 assump_25 =>
    exact assump_25
  apply Or.inl
  intro assump_30
  have assump_46 : (((False ∧ p4) ∧ (p7 → False)) → False) := by
    intro assump_35
    cases assump_35
    case intro assump_36 assump_37 =>
      cases assump_36
      case intro assump_38 assump_39 =>
        apply False.elim assump_38
  let assump_34 := assump_1 assump_46
  apply False.elim assump_34


variable (p6 p4 p1 p5 p0 p7 p2 p3 : Prop)
theorem file8_89320 : (((((p5 ∨ p6) → False) → ((p2 ∧ p6) ∧ (p3 ∨ p3))) ∧ (((p2 ∧ p1) ∨ (False → False)) → False)) → ((((p7 ∨ p0) ∧ (p1 → p2)) ∨ ((p4 → False) ∧ (p4 ∧ p0))) ∨ (((p2 ∧ p6) ∨ (p1 → False)) ∧ ((p1 ∧ p0) ∨ (p6 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    apply And.intro
    apply Or.inr
    intro assump_19
    have assump_41 : ((p2 ∧ p1) ∨ (False → False)) := by
      apply Or.inr
      intro assump_24
      apply False.elim assump_24
    let assump_23 := assump_3 assump_41
    apply False.elim assump_23
    apply Or.inr
    intro assump_30
    have assump_42 : ((p2 ∧ p1) ∨ (False → False)) := by
      apply Or.inr
      intro assump_35
      apply False.elim assump_35
    let assump_34 := assump_3 assump_42
    apply False.elim assump_34


variable (p2 p4 p6 p7 p5 p3 p0 : Prop)
theorem file8_90185 : (((((True ∨ p7) → False) ∨ ((p2 ∨ p2) ∧ (p4 ∧ p2))) ∨ (((p3 ∨ p2) ∨ (False → p4)) → ((p3 ∨ False) → False))) → ((((p2 → False) → (p3 → True)) ∨ ((False → p7) ∨ (p5 ∨ p6))) ∨ (((p7 ∨ p2) ∧ (p6 → p0)) → ((p4 ∨ True) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply Or.inl
      intro assump_8
      intro assump_9
      apply True.intro
    case inr assump_5 =>
      cases assump_5
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            apply Or.inl
            apply Or.inl
            intro assump_22
            intro assump_23
            apply True.intro
        case inr assump_13 =>
          cases assump_11
          case intro assump_26 assump_27 =>
            apply Or.inl
            apply Or.inl
            intro assump_32
            intro assump_33
            apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_36
    intro assump_37
    apply True.intro


variable (p3 p5 p0 p2 p6 p1 p7 : Prop)
theorem file8_91382 : (((((p6 → False) ∨ (True → False)) ∧ ((p3 → False) → (p1 ∨ p2))) ∧ (((p0 ∨ p2) ∨ (p7 ∧ p2)) → ((p0 → False) ∨ (True ∧ p5)))) → ((((p0 → True) → False) ∨ ((p6 → p7) → (p6 → False))) → (((p5 ∧ p1) → (p6 ∨ p5)) ∨ ((p3 ∨ p5) → False)))) := by
  intro assump_13
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    cases assump_13
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_21
        case inl assump_23 =>
          apply Or.inl
          intro assump_31
          cases assump_31
          case intro assump_32 assump_33 =>
            apply Or.inr
            exact assump_32
        case inr assump_24 =>
          apply Or.inl
          intro assump_44
          cases assump_44
          case intro assump_45 assump_46 =>
            apply Or.inr
            exact assump_45
  case inr assump_16 =>
    cases assump_13
    case intro assump_53 assump_54 =>
      cases assump_53
      case intro assump_55 assump_56 =>
        cases assump_55
        case inl assump_57 =>
          apply Or.inl
          intro assump_65
          cases assump_65
          case intro assump_66 assump_67 =>
            apply Or.inr
            exact assump_66
        case inr assump_58 =>
          apply Or.inl
          intro assump_78
          cases assump_78
          case intro assump_79 assump_80 =>
            apply Or.inr
            exact assump_79


variable (p6 p7 p1 : Prop)
theorem file8_92870 : (((((p7 ∨ True) → False) → ((p6 ∨ p1) ∨ (p1 ∧ p1))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p7 ∨ True) → False) → ((p6 ∨ p1) ∨ (p1 ∧ p1))) := by
    intro assump_5
    have assump_16 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p2 p6 p7 p0 p5 p3 : Prop)
theorem file8_93335 : (((((p7 → False) ∨ (p6 ∧ False)) ∧ ((p0 → False) ∨ (p0 → False))) → (((False ∧ True) → False) ∨ ((p3 → True) ∧ (True ∨ p1)))) ∨ ((((p1 → False) → False) ∧ ((p1 → False) → (p2 ∨ p6))) ∧ (((p3 ∨ p7) ∧ (p6 → False)) ∧ ((p3 → p5) ∧ (p2 → p6))))) := by
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
        cases assump_12
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
      case inr assump_9 =>
        apply Or.inl
        intro assump_19
        cases assump_19
        case intro assump_20 assump_21 =>
          apply False.elim assump_20
    case inr assump_5 =>
      cases assump_5
      case intro assump_24 assump_25 =>
        apply False.elim assump_25


variable (p6 p4 p2 p0 p3 p7 p1 : Prop)
theorem file8_94265 : (((((True → False) → (p7 → False)) → False) → False) ∨ ((((p6 ∧ False) ∨ (p7 → False)) ∨ ((p4 ∨ p1) ∨ (p2 ∧ True))) → (((p0 ∨ p3) → False) ∨ ((p0 → p3) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((True → False) → (p7 → False)) := by
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p3 p4 p7 p0 p2 : Prop)
theorem file8_94813 : (((((p6 ∧ True) → False) ∨ ((p0 → p0) ∧ (False → p2))) ∧ (((p4 ∨ True) ∨ (p2 → p0)) → False)) → ((((p4 ∧ p0) → False) ∧ ((p7 ∨ p7) ∧ (p4 → False))) → (((False → p6) → (p4 → False)) ∨ ((p4 → False) → (p3 → p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            apply Or.inl
            intro assump_23
            intro assump_24
            have assump_99 : ((p4 ∨ True) ∨ (p2 → p0)) := by
              apply Or.inl
              apply Or.inl
              exact assump_24
            let assump_31 := assump_16 assump_99
            apply False.elim assump_31
          case inr assump_18 =>
            cases assump_18
            case intro assump_35 assump_36 =>
              apply Or.inl
              intro assump_43
              intro assump_44
              have assump_100 : ((p4 ∨ True) ∨ (p2 → p0)) := by
                apply Or.inl
                apply Or.inl
                exact assump_44
              let assump_51 := assump_16 assump_100
              apply False.elim assump_51
      case inr assump_10 =>
        cases assump_1
        case intro assump_59 assump_60 =>
          cases assump_59
          case inl assump_61 =>
            apply Or.inl
            intro assump_67
            intro assump_68
            have assump_101 : ((p4 ∨ True) ∨ (p2 → p0)) := by
              apply Or.inl
              apply Or.inl
              exact assump_68
            let assump_75 := assump_60 assump_101
            apply False.elim assump_75
          case inr assump_62 =>
            cases assump_62
            case intro assump_79 assump_80 =>
              apply Or.inl
              intro assump_87
              intro assump_88
              have assump_102 : ((p4 ∨ True) ∨ (p2 → p0)) := by
                apply Or.inl
                apply Or.inl
                exact assump_88
              let assump_95 := assump_60 assump_102
              apply False.elim assump_95


variable (p7 p3 p4 p2 : Prop)
theorem file8_97058 : (((((p3 ∨ p7) → False) → ((False → p3) → (p4 → p4))) → (((True ∧ p4) → False) ∧ ((False → False) → False))) → ((((p2 → False) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_26 : (((p3 ∨ p7) → False) → ((False → p3) → (p4 → p4))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    exact assump_10
  let assump_7 := assump_1 assump_26
  let assump_17 := And.right assump_7
  have assump_27 : (False → False) := by
    intro assump_20
    apply False.elim assump_20
  let assump_19 := assump_17 assump_27
  apply False.elim assump_19


variable (p1 p3 p2 p0 p7 p5 : Prop)
theorem file8_97701 : (((((p0 → False) ∧ (False ∧ p7)) ∧ ((p0 → False) ∧ (p5 ∧ p2))) → False) ∨ ((((p2 → False) ∧ (False → p0)) ∧ ((True ∧ p1) → False)) → (((p3 → True) ∧ (p2 ∨ p0)) → ((p2 ∨ p1) → False)))) := by
  apply Or.inl
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_19
      case intro assump_22 assump_23 =>
        apply False.elim assump_22


