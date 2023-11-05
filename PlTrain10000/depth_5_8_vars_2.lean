variable (p5 p0 p7 p1 p6 p2 p4 : Prop)
theorem file2_47 : (((((True ∧ True) ∨ (p7 → False)) ∨ ((p7 ∨ p1) ∨ (p1 ∨ p0))) → False) → ((((p0 ∨ p2) → (p4 ∧ p0)) ∧ ((False → p7) ∧ (p7 ∨ p2))) → (((False → False) ∧ (p5 → False)) ∧ ((p6 → False) ∧ (p7 ∨ p6))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_10
    case intro assump_13 assump_14 =>
      cases assump_14
      case inl assump_17 =>
        have assump_86 : (((True ∧ True) ∨ (p7 → False)) ∨ ((p7 ∨ p1) ∨ (p1 ∨ p0))) := by
          apply Or.inl
          apply Or.inl
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_23 := assump_1 assump_86
        apply False.elim assump_23
      case inr assump_18 =>
        have assump_87 : (((True ∧ True) ∨ (p7 → False)) ∨ ((p7 ∨ p1) ∨ (p1 ∨ p0))) := by
          apply Or.inl
          apply Or.inl
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_31 := assump_1 assump_87
        apply False.elim assump_31
  apply And.intro
  intro assump_35
  cases assump_2
  case intro assump_38 assump_39 =>
    cases assump_39
    case intro assump_42 assump_43 =>
      cases assump_43
      case inl assump_46 =>
        have assump_88 : (((True ∧ True) ∨ (p7 → False)) ∨ ((p7 ∨ p1) ∨ (p1 ∨ p0))) := by
          apply Or.inl
          apply Or.inl
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_52 := assump_1 assump_88
        apply False.elim assump_52
      case inr assump_47 =>
        have assump_89 : (((True ∧ True) ∨ (p7 → False)) ∨ ((p7 ∨ p1) ∨ (p1 ∨ p0))) := by
          apply Or.inl
          apply Or.inl
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_60 := assump_1 assump_89
        apply False.elim assump_60
  cases assump_2
  case intro assump_64 assump_65 =>
    cases assump_65
    case intro assump_68 assump_69 =>
      cases assump_69
      case inl assump_72 =>
        apply Or.inl
        exact assump_72
      case inr assump_73 =>
        have assump_90 : (((True ∧ True) ∨ (p7 → False)) ∨ ((p7 ∨ p1) ∨ (p1 ∨ p0))) := by
          apply Or.inl
          apply Or.inl
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_82 := assump_1 assump_90
        apply False.elim assump_82


variable (p0 p2 p6 p4 p1 : Prop)
theorem file2_2560 : (((((True → p0) → (p2 → False)) → ((False ∧ p6) → (p1 ∧ p2))) ∧ (((True ∨ p0) → False) ∧ ((p2 ∨ p4) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : (True ∨ p0) := by
        apply Or.inl
        apply True.intro
      let assump_13 := assump_6 assump_17
      apply False.elim assump_13


variable (p4 p0 p3 p5 p2 p6 : Prop)
theorem file2_3031 : (((((p2 ∧ p0) → (p3 ∧ p4)) ∧ ((False → False) → False)) → False) ∨ ((((p3 → False) ∨ (True ∨ p6)) ∨ ((p5 ∧ p2) → (p0 → False))) → False)) := by
  apply Or.inl
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    have assump_45 : (False → False) := by
      intro assump_39
      apply False.elim assump_39
    let assump_38 := assump_33 assump_45
    apply False.elim assump_38


variable (p6 p7 p0 p5 p3 p2 : Prop)
theorem file2_3492 : (((((p5 ∨ p0) → (True → True)) → False) → (((p7 → False) → (p2 → p5)) ∧ ((True ∧ p5) ∧ (p3 ∧ p7)))) ∨ ((((p3 → p3) → (False → False)) → False) ∧ (((p7 → False) → (p0 ∨ p6)) ∧ ((p5 ∧ p2) ∨ (True → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  have assump_40 : ((p5 ∨ p0) → (True → True)) := by
    intro assump_11
    intro assump_12
    apply True.intro
  let assump_10 := assump_1 assump_40
  apply False.elim assump_10
  apply And.intro
  apply And.intro
  apply True.intro
  have assump_41 : ((p5 ∨ p0) → (True → True)) := by
    intro assump_19
    intro assump_20
    apply True.intro
  let assump_18 := assump_1 assump_41
  apply False.elim assump_18
  apply And.intro
  have assump_42 : ((p5 ∨ p0) → (True → True)) := by
    intro assump_27
    intro assump_28
    apply True.intro
  let assump_26 := assump_1 assump_42
  apply False.elim assump_26
  have assump_43 : ((p5 ∨ p0) → (True → True)) := by
    intro assump_35
    intro assump_36
    apply True.intro
  let assump_34 := assump_1 assump_43
  apply False.elim assump_34


variable (p4 p5 p7 p3 p2 p0 : Prop)
theorem file2_4646 : (((((p2 ∧ False) ∧ (p3 → False)) ∧ ((False → False) → (p7 → False))) ∧ (((True ∧ p7) ∨ (p0 ∨ p7)) ∨ ((p0 ∧ p4) ∧ (p5 → False)))) ∨ ((((True → False) ∧ (True ∨ p3)) → ((p7 → False) ∧ (True ∧ p0))) ∨ (((p4 → False) → False) ∧ ((True ∨ p5) ∧ (False → False))))) := by
  apply Or.inr
  apply Or.inl
  intro assump_17
  apply And.intro
  intro assump_18
  cases assump_17
  case intro assump_21 assump_22 =>
    cases assump_22
    case inl assump_25 =>
      have assump_59 : True := by
        apply True.intro
      let assump_29 := assump_21 assump_59
      apply False.elim assump_29
    case inr assump_26 =>
      have assump_60 : True := by
        apply True.intro
      let assump_36 := assump_21 assump_60
      apply False.elim assump_36
  apply And.intro
  apply True.intro
  cases assump_17
  case intro assump_40 assump_41 =>
    cases assump_41
    case inl assump_44 =>
      have assump_61 : True := by
        apply True.intro
      let assump_48 := assump_40 assump_61
      apply False.elim assump_48
    case inr assump_45 =>
      have assump_62 : True := by
        apply True.intro
      let assump_55 := assump_40 assump_62
      apply False.elim assump_55


variable (p7 p2 p5 p4 p1 : Prop)
theorem file2_5881 : (((((False ∧ p2) → False) ∨ ((p4 ∧ p5) → (p7 ∨ p1))) → False) → False) := by
  intro assump_1
  have assump_13 : (((False ∧ p2) → False) ∨ ((p4 ∧ p5) → (p7 ∨ p1))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p7 p3 p4 p1 p0 : Prop)
theorem file2_6299 : (((((p0 → True) → (p4 ∨ p1)) ∨ ((p3 ∧ p3) ∨ (p3 → False))) ∨ (((True ∧ p3) ∧ (p7 ∧ p7)) → ((True ∨ p5) ∧ (p4 ∨ p1)))) → ((((p0 ∨ True) → False) → False) ∨ (((p3 → False) → (False → p4)) ∨ ((p4 → True) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      have assump_48 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_11 := assump_8 assump_48
      apply False.elim assump_11
    case inr assump_5 =>
      cases assump_5
      case inl assump_15 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          apply Or.inl
          intro assump_23
          have assump_49 : (p0 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_26 := assump_23 assump_49
          apply False.elim assump_26
      case inr assump_16 =>
        apply Or.inl
        intro assump_32
        have assump_50 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_35 := assump_32 assump_50
        apply False.elim assump_35
  case inr assump_3 =>
    apply Or.inl
    intro assump_41
    have assump_51 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_44 := assump_41 assump_51
    apply False.elim assump_44


variable (p0 p3 p7 p1 p2 p4 : Prop)
theorem file2_7712 : (((((True → p4) → (p7 ∧ p7)) ∧ ((p0 → False) ∧ (p4 ∧ p3))) ∨ (((p7 → p7) ∧ (p1 → p7)) ∧ ((True → False) ∨ (False → False)))) → ((((p3 → False) → (p7 → p7)) ∨ ((p3 ∨ p7) ∨ (p7 → False))) → (((False → p2) ∨ (False → True)) ∨ ((True ∨ p0) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_10
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            apply Or.inl
            apply Or.inl
            intro assump_23
            apply False.elim assump_23
    case inr assump_8 =>
      cases assump_8
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_27
          case inl assump_34 =>
            apply Or.inl
            apply Or.inl
            intro assump_38
            apply False.elim assump_38
          case inr assump_35 =>
            apply Or.inl
            apply Or.inl
            intro assump_43
            apply False.elim assump_43
  case inr assump_4 =>
    cases assump_4
    case inl assump_46 =>
      cases assump_46
      case inl assump_48 =>
        cases assump_1
        case inl assump_52 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_55
            case intro assump_58 assump_59 =>
              cases assump_59
              case intro assump_62 assump_63 =>
                apply Or.inl
                apply Or.inl
                intro assump_68
                apply False.elim assump_68
        case inr assump_53 =>
          cases assump_53
          case intro assump_71 assump_72 =>
            cases assump_71
            case intro assump_73 assump_74 =>
              cases assump_72
              case inl assump_79 =>
                apply Or.inl
                apply Or.inl
                intro assump_83
                apply False.elim assump_83
              case inr assump_80 =>
                apply Or.inl
                apply Or.inl
                intro assump_88
                apply False.elim assump_88
      case inr assump_49 =>
        cases assump_1
        case inl assump_93 =>
          cases assump_93
          case intro assump_95 assump_96 =>
            cases assump_96
            case intro assump_99 assump_100 =>
              cases assump_100
              case intro assump_103 assump_104 =>
                apply Or.inl
                apply Or.inl
                intro assump_109
                apply False.elim assump_109
        case inr assump_94 =>
          cases assump_94
          case intro assump_112 assump_113 =>
            cases assump_112
            case intro assump_114 assump_115 =>
              cases assump_113
              case inl assump_120 =>
                apply Or.inl
                apply Or.inl
                intro assump_124
                apply False.elim assump_124
              case inr assump_121 =>
                apply Or.inl
                apply Or.inl
                intro assump_129
                apply False.elim assump_129
    case inr assump_47 =>
      cases assump_1
      case inl assump_134 =>
        cases assump_134
        case intro assump_136 assump_137 =>
          cases assump_137
          case intro assump_140 assump_141 =>
            cases assump_141
            case intro assump_144 assump_145 =>
              apply Or.inl
              apply Or.inl
              intro assump_150
              apply False.elim assump_150
      case inr assump_135 =>
        cases assump_135
        case intro assump_153 assump_154 =>
          cases assump_153
          case intro assump_155 assump_156 =>
            cases assump_154
            case inl assump_161 =>
              apply Or.inl
              apply Or.inl
              intro assump_165
              apply False.elim assump_165
            case inr assump_162 =>
              apply Or.inl
              apply Or.inl
              intro assump_170
              apply False.elim assump_170


variable (p4 p1 p3 p7 p5 p6 p2 : Prop)
theorem file2_11946 : ((((((p2 → False) → (True → False)) → ((p4 → p2) → (False ∧ p2))) ∧ (((p7 → False) → (p7 ∧ p7)) → ((p3 ∧ True) → (p2 → False)))) ∧ ((((p4 → True) ∧ (p5 ∧ p2)) ∨ ((False ∨ p6) ∧ (p4 → p2))) ∧ (((False ∧ p4) ∧ (False → p4)) ∧ ((p4 → False) ∧ (p1 ∧ p7))))) → False) := by
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
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_11
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    apply False.elim assump_28
        case inr assump_13 =>
          cases assump_13
          case intro assump_32 assump_33 =>
            cases assump_32
            case inl assump_34 =>
              apply False.elim assump_34
            case inr assump_35 =>
              cases assump_11
              case intro assump_42 assump_43 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  cases assump_44
                  case intro assump_46 assump_47 =>
                    apply False.elim assump_46


variable (p0 p5 p1 p4 p3 p7 : Prop)
theorem file2_13480 : ((((((p1 ∧ True) ∧ (p4 ∧ p0)) ∧ ((p3 → p3) → (p0 → False))) → (((p1 ∧ p7) ∨ (p5 → False)) → ((p1 ∨ p0) ∧ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_121 : ((((p1 ∧ True) ∧ (p4 ∧ p0)) ∧ ((p3 → p3) → (p0 → False))) → (((p1 ∧ p7) ∨ (p5 → False)) → ((p1 ∨ p0) ∧ (p0 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_5
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_18
              case intro assump_25 assump_26 =>
                apply Or.inl
                exact assump_19
    case inr assump_8 =>
      cases assump_5
      case intro assump_35 assump_36 =>
        cases assump_35
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            cases assump_38
            case intro assump_45 assump_46 =>
              apply Or.inl
              exact assump_39
    intro assump_53
    cases assump_6
    case inl assump_56 =>
      cases assump_56
      case intro assump_58 assump_59 =>
        cases assump_5
        case intro assump_64 assump_65 =>
          cases assump_64
          case intro assump_66 assump_67 =>
            cases assump_66
            case intro assump_68 assump_69 =>
              cases assump_67
              case intro assump_74 assump_75 =>
                have assump_122 : (p3 → p3) := by
                  intro assump_83
                  exact assump_83
                let assump_82 := assump_65 assump_122
                have assump_123 : p0 := by
                  exact assump_75
                let assump_86 := assump_82 assump_123
                apply False.elim assump_86
    case inr assump_57 =>
      cases assump_5
      case intro assump_92 assump_93 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          cases assump_94
          case intro assump_96 assump_97 =>
            cases assump_95
            case intro assump_102 assump_103 =>
              have assump_124 : (p3 → p3) := by
                intro assump_111
                exact assump_111
              let assump_110 := assump_93 assump_124
              have assump_125 : p0 := by
                exact assump_103
              let assump_114 := assump_110 assump_125
              apply False.elim assump_114
  let assump_4 := assump_1 assump_121
  apply False.elim assump_4


variable (p0 p5 p2 p4 p3 p1 : Prop)
theorem file2_16172 : ((((((p5 ∨ p2) ∨ (p0 ∨ p0)) → ((p2 → False) ∨ (p3 ∧ p1))) → False) ∧ ((((True ∧ True) ∨ (p5 → True)) ∨ ((p4 ∧ p1) ∨ (p0 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (((True ∧ True) ∨ (p5 → True)) ∨ ((p4 ∧ p1) ∨ (p0 ∧ p2))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p3 p0 p5 p6 p7 : Prop)
theorem file2_16710 : (((((p6 → False) ∨ (p7 ∨ p5)) → ((p5 ∨ p6) → (p3 ∨ p7))) ∧ (((p7 ∨ p0) ∨ (p6 → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((p7 ∨ p0) ∨ (p6 → True)) := by
      apply Or.inr
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p6 p7 p5 p4 p3 p1 p2 p0 : Prop)
theorem file2_17140 : (((((p2 → p5) ∨ (p4 → p4)) ∨ ((p2 ∧ p6) ∨ (p4 ∨ p2))) → (((p5 → False) ∨ (p1 → p3)) → ((p4 → False) → (p6 ∨ True)))) ∨ ((((p1 ∧ p4) → (p3 ∧ p7)) ∨ ((True → True) → False)) ∧ (((p2 ∨ p0) → False) ∧ ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_6
  case inl assump_10 =>
    cases assump_5
    case inl assump_14 =>
      cases assump_14
      case inl assump_16 =>
        apply Or.inr
        apply True.intro
      case inr assump_17 =>
        apply Or.inr
        apply True.intro
    case inr assump_15 =>
      cases assump_15
      case inl assump_22 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          apply Or.inl
          exact assump_25
      case inr assump_23 =>
        cases assump_23
        case inl assump_30 =>
          apply Or.inr
          apply True.intro
        case inr assump_31 =>
          apply Or.inr
          apply True.intro
  case inr assump_11 =>
    cases assump_5
    case inl assump_38 =>
      cases assump_38
      case inl assump_40 =>
        apply Or.inr
        apply True.intro
      case inr assump_41 =>
        apply Or.inr
        apply True.intro
    case inr assump_39 =>
      cases assump_39
      case inl assump_46 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          apply Or.inl
          exact assump_49
      case inr assump_47 =>
        cases assump_47
        case inl assump_54 =>
          apply Or.inr
          apply True.intro
        case inr assump_55 =>
          apply Or.inr
          apply True.intro


variable (p1 p6 p2 p5 p3 : Prop)
theorem file2_18793 : (((((p5 ∨ p6) ∨ (False → False)) → False) → False) ∨ ((((p6 → False) ∨ (False → False)) → False) → (((False ∨ p5) → (p1 ∨ p3)) → ((p6 ∧ p2) ∨ (p1 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p5 ∨ p6) ∨ (False → False)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p5 p3 p6 p2 : Prop)
theorem file2_19233 : (((((p6 ∨ p5) → (p3 ∨ p3)) ∨ ((p7 ∨ p6) → False)) → (((p2 ∧ True) ∨ (False → p2)) ∨ ((False → False) → False))) → ((((True ∨ False) → False) → False) ∨ (((True → p6) → False) → ((p6 → p2) → False)))) := by
  intro assump_7
  apply Or.inl
  intro assump_10
  have assump_17 : (True ∨ False) := by
    apply Or.inl
    apply True.intro
  let assump_13 := assump_10 assump_17
  apply False.elim assump_13


variable (p5 p6 : Prop)
theorem file2_19683 : (((((p5 ∨ p6) → (p5 → False)) → ((True → False) → False)) → False) → False) := by
  intro assump_1
  have assump_19 : (((p5 ∨ p6) → (p5 → False)) → ((True → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_20 : True := by
      apply True.intro
    let assump_12 := assump_6 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p0 p2 p5 p4 p3 p1 : Prop)
theorem file2_20155 : (((((p5 → p3) ∨ (p4 → False)) ∨ ((p3 → p4) ∧ (p0 → p5))) ∨ (((False ∨ p2) ∨ (p2 → p3)) ∧ ((p0 ∧ p3) → (p2 ∨ p0)))) → ((((p6 ∨ p2) ∧ (p6 ∧ False)) ∧ ((p1 → False) → (False → True))) → (((True ∧ p6) ∧ (p1 → False)) ∧ ((p6 ∨ False) ∧ (p4 ∨ p4))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  apply And.intro
  apply True.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          apply False.elim assump_12
      case inr assump_8 =>
        cases assump_6
        case intro assump_19 assump_20 =>
          apply False.elim assump_20
  intro assump_25
  cases assump_2
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      cases assump_30
      case inl assump_32 =>
        cases assump_31
        case intro assump_36 assump_37 =>
          apply False.elim assump_37
      case inr assump_33 =>
        cases assump_31
        case intro assump_44 assump_45 =>
          apply False.elim assump_45
  apply And.intro
  cases assump_2
  case intro assump_50 assump_51 =>
    cases assump_50
    case intro assump_52 assump_53 =>
      cases assump_52
      case inl assump_54 =>
        cases assump_53
        case intro assump_58 assump_59 =>
          apply False.elim assump_59
      case inr assump_55 =>
        cases assump_53
        case intro assump_66 assump_67 =>
          apply False.elim assump_67
  cases assump_2
  case intro assump_72 assump_73 =>
    cases assump_72
    case intro assump_74 assump_75 =>
      cases assump_74
      case inl assump_76 =>
        cases assump_75
        case intro assump_80 assump_81 =>
          apply False.elim assump_81
      case inr assump_77 =>
        cases assump_75
        case intro assump_88 assump_89 =>
          apply False.elim assump_89


variable (p3 p2 p6 p5 p1 : Prop)
theorem file2_22176 : ((((((False → p3) ∧ (True → False)) → ((True ∨ p5) → False)) → (((False ∧ p5) → (p1 → False)) ∧ ((p6 → True) ∨ (p2 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False → p3) ∧ (True → False)) → ((True ∨ p5) → False)) → (((False ∧ p5) → (p1 → False)) ∧ ((p6 → True) ∨ (p2 ∧ p2)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
    apply Or.inl
    intro assump_16
    apply True.intro
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 p4 p2 p5 p7 p0 : Prop)
theorem file2_22838 : (((((p5 → p4) ∧ (p1 → False)) ∧ ((False → p1) → False)) ∧ (((p2 ∨ p7) → False) ∧ ((p0 → p5) ∧ (p5 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            have assump_34 : (False → p1) := by
              intro assump_28
              apply False.elim assump_28
            let assump_27 := assump_5 assump_34
            apply False.elim assump_27


variable (p4 p2 p6 p0 : Prop)
theorem file2_23540 : ((((((False ∧ False) → (p4 ∧ False)) ∨ ((p4 → False) ∧ (True ∨ p2))) ∨ (((True → False) → False) → ((p6 ∨ p4) ∧ (p0 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((False ∧ False) → (p4 ∧ False)) ∨ ((p4 → False) ∧ (True ∨ p2))) ∨ (((True → False) → False) → ((p6 ∨ p4) ∧ (p0 ∧ False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    cases assump_5
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p1 p5 p0 p7 p6 p2 p4 : Prop)
theorem file2_24238 : (((((p1 ∧ p7) ∧ (p1 → p1)) ∧ ((p4 → p0) ∨ (p5 ∧ p7))) → (((True → False) ∨ (p4 → False)) → ((p6 → p5) → (p0 → False)))) → ((((False ∧ p6) → (p0 ∨ p1)) ∨ ((p4 ∧ True) ∨ (p6 ∨ p5))) ∨ (((p2 ∨ p4) ∨ (p5 ∨ p4)) ∨ ((False → False) → False)))) := by
  intro assump_25
  apply Or.inl
  apply Or.inl
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    apply False.elim assump_29


variable (p4 p7 p3 p6 p2 p1 p5 : Prop)
theorem file2_24696 : (((((True → False) → False) → False) → (((p4 → False) → False) → ((True → False) ∨ (p1 → True)))) ∨ ((((p4 ∨ p2) ∨ (False → False)) → ((p7 ∧ p3) ∨ (p5 → False))) ∨ (((p2 ∧ p6) ∧ (p7 → p2)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  have assump_21 : ((True → False) → False) := by
    intro assump_11
    have assump_22 : True := by
      apply True.intro
    let assump_14 := assump_11 assump_22
    apply False.elim assump_14
  let assump_10 := assump_1 assump_21
  apply False.elim assump_10


variable (p0 p7 p6 p5 p3 : Prop)
theorem file2_25304 : ((((((False → p7) → False) ∧ ((p0 → p6) ∨ (p5 → p3))) → False) → False) → False) := by
  intro assump_1
  have assump_35 : ((((False → p7) → False) ∧ ((p0 → p6) ∨ (p5 → p3))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_36 : (False → p7) := by
          intro assump_16
          apply False.elim assump_16
        let assump_15 := assump_6 assump_36
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_37 : (False → p7) := by
          intro assump_26
          apply False.elim assump_26
        let assump_25 := assump_6 assump_37
        apply False.elim assump_25
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p7 p4 p1 p3 p6 p5 : Prop)
theorem file2_26142 : ((((((p3 ∧ p7) ∨ (p1 ∨ p4)) ∧ ((p5 → False) ∧ (False ∨ p4))) → (((True → False) ∧ (False ∧ False)) → ((p7 ∧ p6) ∧ (p7 → p6)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p3 ∧ p7) ∨ (p1 ∨ p4)) ∧ ((p5 → False) ∧ (False ∨ p4))) → (((True → False) ∧ (False ∧ False)) → ((p7 ∧ p6) ∧ (p7 → p6)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
    cases assump_6
    case intro assump_15 assump_16 =>
      cases assump_16
      case intro assump_19 assump_20 =>
        apply False.elim assump_19
    intro assump_23
    cases assump_6
    case intro assump_26 assump_27 =>
      cases assump_27
      case intro assump_30 assump_31 =>
        apply False.elim assump_30
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p0 p2 p7 p3 p4 p5 p6 p1 : Prop)
theorem file2_27148 : (((((p1 ∧ True) → (p2 ∨ p2)) ∧ ((p6 ∧ False) → False)) → (((p0 → p7) ∧ (p0 ∨ p0)) → ((p1 ∧ False) → False))) ∨ ((((p3 ∧ p0) → (p0 ∨ p5)) ∨ ((p0 ∧ False) ∧ (p4 → True))) → (((True ∨ p5) ∨ (p5 → p3)) ∧ ((p3 → False) ∧ (p2 ∧ p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_5


variable (p6 p2 p0 p7 p3 : Prop)
theorem file2_27588 : ((((((p3 → False) ∨ (p0 → False)) ∧ ((p2 ∧ False) → False)) → (((False → False) ∧ (False → False)) ∨ ((p6 ∧ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p3 → False) ∨ (p0 → False)) ∧ ((p2 ∧ False) → False)) → (((False → False) ∧ (False → False)) ∨ ((p6 ∧ p7) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        apply And.intro
        intro assump_14
        apply False.elim assump_14
        intro assump_17
        apply False.elim assump_17
      case inr assump_9 =>
        apply Or.inl
        apply And.intro
        intro assump_24
        apply False.elim assump_24
        intro assump_27
        apply False.elim assump_27
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p0 p3 p2 p6 p1 p7 p5 : Prop)
theorem file2_28501 : (((((p3 ∧ p7) ∨ (p7 ∧ p1)) ∧ ((p5 → False) → False)) ∧ (((p5 ∧ p7) ∧ (p5 ∧ p1)) ∧ ((p1 ∨ p1) → False))) → ((((True ∧ p6) → False) ∨ ((p3 ∨ p0) ∧ (p0 → False))) → (((False → False) ∨ (True ∨ p2)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_1
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_13
              case intro assump_26 assump_27 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_29
                    case intro assump_36 assump_37 =>
                      have assump_656 : (p1 ∨ p1) := by
                        apply Or.inl
                        exact assump_37
                      let assump_44 := assump_27 assump_656
                      apply False.elim assump_44
          case inr assump_17 =>
            cases assump_17
            case intro assump_48 assump_49 =>
              cases assump_13
              case intro assump_56 assump_57 =>
                cases assump_56
                case intro assump_58 assump_59 =>
                  cases assump_58
                  case intro assump_60 assump_61 =>
                    cases assump_59
                    case intro assump_66 assump_67 =>
                      have assump_657 : (p1 ∨ p1) := by
                        apply Or.inl
                        exact assump_67
                      let assump_74 := assump_57 assump_657
                      apply False.elim assump_74
    case inr assump_9 =>
      cases assump_9
      case intro assump_78 assump_79 =>
        cases assump_78
        case inl assump_80 =>
          cases assump_1
          case intro assump_86 assump_87 =>
            cases assump_86
            case intro assump_88 assump_89 =>
              cases assump_88
              case inl assump_90 =>
                cases assump_90
                case intro assump_92 assump_93 =>
                  cases assump_87
                  case intro assump_100 assump_101 =>
                    cases assump_100
                    case intro assump_102 assump_103 =>
                      cases assump_102
                      case intro assump_104 assump_105 =>
                        cases assump_103
                        case intro assump_110 assump_111 =>
                          have assump_658 : (p1 ∨ p1) := by
                            apply Or.inl
                            exact assump_111
                          let assump_118 := assump_101 assump_658
                          apply False.elim assump_118
              case inr assump_91 =>
                cases assump_91
                case intro assump_122 assump_123 =>
                  cases assump_87
                  case intro assump_130 assump_131 =>
                    cases assump_130
                    case intro assump_132 assump_133 =>
                      cases assump_132
                      case intro assump_134 assump_135 =>
                        cases assump_133
                        case intro assump_140 assump_141 =>
                          have assump_659 : (p1 ∨ p1) := by
                            apply Or.inl
                            exact assump_141
                          let assump_148 := assump_131 assump_659
                          apply False.elim assump_148
        case inr assump_81 =>
          cases assump_1
          case intro assump_156 assump_157 =>
            cases assump_156
            case intro assump_158 assump_159 =>
              cases assump_158
              case inl assump_160 =>
                cases assump_160
                case intro assump_162 assump_163 =>
                  cases assump_157
                  case intro assump_170 assump_171 =>
                    cases assump_170
                    case intro assump_172 assump_173 =>
                      cases assump_172
                      case intro assump_174 assump_175 =>
                        cases assump_173
                        case intro assump_180 assump_181 =>
                          have assump_660 : (p1 ∨ p1) := by
                            apply Or.inl
                            exact assump_181
                          let assump_188 := assump_171 assump_660
                          apply False.elim assump_188
              case inr assump_161 =>
                cases assump_161
                case intro assump_192 assump_193 =>
                  cases assump_157
                  case intro assump_200 assump_201 =>
                    cases assump_200
                    case intro assump_202 assump_203 =>
                      cases assump_202
                      case intro assump_204 assump_205 =>
                        cases assump_203
                        case intro assump_210 assump_211 =>
                          have assump_661 : (p1 ∨ p1) := by
                            apply Or.inl
                            exact assump_211
                          let assump_218 := assump_201 assump_661
                          apply False.elim assump_218
  case inr assump_5 =>
    cases assump_5
    case inl assump_222 =>
      cases assump_2
      case inl assump_226 =>
        cases assump_1
        case intro assump_230 assump_231 =>
          cases assump_230
          case intro assump_232 assump_233 =>
            cases assump_232
            case inl assump_234 =>
              cases assump_234
              case intro assump_236 assump_237 =>
                cases assump_231
                case intro assump_244 assump_245 =>
                  cases assump_244
                  case intro assump_246 assump_247 =>
                    cases assump_246
                    case intro assump_248 assump_249 =>
                      cases assump_247
                      case intro assump_254 assump_255 =>
                        have assump_662 : (p1 ∨ p1) := by
                          apply Or.inl
                          exact assump_255
                        let assump_262 := assump_245 assump_662
                        apply False.elim assump_262
            case inr assump_235 =>
              cases assump_235
              case intro assump_266 assump_267 =>
                cases assump_231
                case intro assump_274 assump_275 =>
                  cases assump_274
                  case intro assump_276 assump_277 =>
                    cases assump_276
                    case intro assump_278 assump_279 =>
                      cases assump_277
                      case intro assump_284 assump_285 =>
                        have assump_663 : (p1 ∨ p1) := by
                          apply Or.inl
                          exact assump_285
                        let assump_292 := assump_275 assump_663
                        apply False.elim assump_292
      case inr assump_227 =>
        cases assump_227
        case intro assump_296 assump_297 =>
          cases assump_296
          case inl assump_298 =>
            cases assump_1
            case intro assump_304 assump_305 =>
              cases assump_304
              case intro assump_306 assump_307 =>
                cases assump_306
                case inl assump_308 =>
                  cases assump_308
                  case intro assump_310 assump_311 =>
                    cases assump_305
                    case intro assump_318 assump_319 =>
                      cases assump_318
                      case intro assump_320 assump_321 =>
                        cases assump_320
                        case intro assump_322 assump_323 =>
                          cases assump_321
                          case intro assump_328 assump_329 =>
                            have assump_664 : (p1 ∨ p1) := by
                              apply Or.inl
                              exact assump_329
                            let assump_336 := assump_319 assump_664
                            apply False.elim assump_336
                case inr assump_309 =>
                  cases assump_309
                  case intro assump_340 assump_341 =>
                    cases assump_305
                    case intro assump_348 assump_349 =>
                      cases assump_348
                      case intro assump_350 assump_351 =>
                        cases assump_350
                        case intro assump_352 assump_353 =>
                          cases assump_351
                          case intro assump_358 assump_359 =>
                            have assump_665 : (p1 ∨ p1) := by
                              apply Or.inl
                              exact assump_359
                            let assump_366 := assump_349 assump_665
                            apply False.elim assump_366
          case inr assump_299 =>
            cases assump_1
            case intro assump_374 assump_375 =>
              cases assump_374
              case intro assump_376 assump_377 =>
                cases assump_376
                case inl assump_378 =>
                  cases assump_378
                  case intro assump_380 assump_381 =>
                    cases assump_375
                    case intro assump_388 assump_389 =>
                      cases assump_388
                      case intro assump_390 assump_391 =>
                        cases assump_390
                        case intro assump_392 assump_393 =>
                          cases assump_391
                          case intro assump_398 assump_399 =>
                            have assump_666 : (p1 ∨ p1) := by
                              apply Or.inl
                              exact assump_399
                            let assump_406 := assump_389 assump_666
                            apply False.elim assump_406
                case inr assump_379 =>
                  cases assump_379
                  case intro assump_410 assump_411 =>
                    cases assump_375
                    case intro assump_418 assump_419 =>
                      cases assump_418
                      case intro assump_420 assump_421 =>
                        cases assump_420
                        case intro assump_422 assump_423 =>
                          cases assump_421
                          case intro assump_428 assump_429 =>
                            have assump_667 : (p1 ∨ p1) := by
                              apply Or.inl
                              exact assump_429
                            let assump_436 := assump_419 assump_667
                            apply False.elim assump_436
    case inr assump_223 =>
      cases assump_2
      case inl assump_442 =>
        cases assump_1
        case intro assump_446 assump_447 =>
          cases assump_446
          case intro assump_448 assump_449 =>
            cases assump_448
            case inl assump_450 =>
              cases assump_450
              case intro assump_452 assump_453 =>
                cases assump_447
                case intro assump_460 assump_461 =>
                  cases assump_460
                  case intro assump_462 assump_463 =>
                    cases assump_462
                    case intro assump_464 assump_465 =>
                      cases assump_463
                      case intro assump_470 assump_471 =>
                        have assump_668 : (p1 ∨ p1) := by
                          apply Or.inl
                          exact assump_471
                        let assump_478 := assump_461 assump_668
                        apply False.elim assump_478
            case inr assump_451 =>
              cases assump_451
              case intro assump_482 assump_483 =>
                cases assump_447
                case intro assump_490 assump_491 =>
                  cases assump_490
                  case intro assump_492 assump_493 =>
                    cases assump_492
                    case intro assump_494 assump_495 =>
                      cases assump_493
                      case intro assump_500 assump_501 =>
                        have assump_669 : (p1 ∨ p1) := by
                          apply Or.inl
                          exact assump_501
                        let assump_508 := assump_491 assump_669
                        apply False.elim assump_508
      case inr assump_443 =>
        cases assump_443
        case intro assump_512 assump_513 =>
          cases assump_512
          case inl assump_514 =>
            cases assump_1
            case intro assump_520 assump_521 =>
              cases assump_520
              case intro assump_522 assump_523 =>
                cases assump_522
                case inl assump_524 =>
                  cases assump_524
                  case intro assump_526 assump_527 =>
                    cases assump_521
                    case intro assump_534 assump_535 =>
                      cases assump_534
                      case intro assump_536 assump_537 =>
                        cases assump_536
                        case intro assump_538 assump_539 =>
                          cases assump_537
                          case intro assump_544 assump_545 =>
                            have assump_670 : (p1 ∨ p1) := by
                              apply Or.inl
                              exact assump_545
                            let assump_552 := assump_535 assump_670
                            apply False.elim assump_552
                case inr assump_525 =>
                  cases assump_525
                  case intro assump_556 assump_557 =>
                    cases assump_521
                    case intro assump_564 assump_565 =>
                      cases assump_564
                      case intro assump_566 assump_567 =>
                        cases assump_566
                        case intro assump_568 assump_569 =>
                          cases assump_567
                          case intro assump_574 assump_575 =>
                            have assump_671 : (p1 ∨ p1) := by
                              apply Or.inl
                              exact assump_575
                            let assump_582 := assump_565 assump_671
                            apply False.elim assump_582
          case inr assump_515 =>
            cases assump_1
            case intro assump_590 assump_591 =>
              cases assump_590
              case intro assump_592 assump_593 =>
                cases assump_592
                case inl assump_594 =>
                  cases assump_594
                  case intro assump_596 assump_597 =>
                    cases assump_591
                    case intro assump_604 assump_605 =>
                      cases assump_604
                      case intro assump_606 assump_607 =>
                        cases assump_606
                        case intro assump_608 assump_609 =>
                          cases assump_607
                          case intro assump_614 assump_615 =>
                            have assump_672 : (p1 ∨ p1) := by
                              apply Or.inl
                              exact assump_615
                            let assump_622 := assump_605 assump_672
                            apply False.elim assump_622
                case inr assump_595 =>
                  cases assump_595
                  case intro assump_626 assump_627 =>
                    cases assump_591
                    case intro assump_634 assump_635 =>
                      cases assump_634
                      case intro assump_636 assump_637 =>
                        cases assump_636
                        case intro assump_638 assump_639 =>
                          cases assump_637
                          case intro assump_644 assump_645 =>
                            have assump_673 : (p1 ∨ p1) := by
                              apply Or.inl
                              exact assump_645
                            let assump_652 := assump_635 assump_673
                            apply False.elim assump_652


variable (p3 p2 p4 p5 : Prop)
theorem file2_45025 : ((((((p2 → False) ∨ (p2 ∨ p5)) ∨ ((p3 → p4) → False)) → (((False → False) ∧ (False → False)) ∨ ((p3 → False) ∧ (p4 ∨ p5)))) → False) → False) := by
  intro assump_57
  have assump_103 : ((((p2 → False) ∨ (p2 ∨ p5)) ∨ ((p3 → p4) → False)) → (((False → False) ∧ (False → False)) ∨ ((p3 → False) ∧ (p4 ∨ p5)))) := by
    intro assump_61
    cases assump_61
    case inl assump_62 =>
      cases assump_62
      case inl assump_64 =>
        apply Or.inl
        apply And.intro
        intro assump_68
        apply False.elim assump_68
        intro assump_71
        apply False.elim assump_71
      case inr assump_65 =>
        cases assump_65
        case inl assump_74 =>
          apply Or.inl
          apply And.intro
          intro assump_78
          apply False.elim assump_78
          intro assump_81
          apply False.elim assump_81
        case inr assump_75 =>
          apply Or.inl
          apply And.intro
          intro assump_86
          apply False.elim assump_86
          intro assump_89
          apply False.elim assump_89
    case inr assump_63 =>
      apply Or.inl
      apply And.intro
      intro assump_94
      apply False.elim assump_94
      intro assump_97
      apply False.elim assump_97
  let assump_60 := assump_57 assump_103
  apply False.elim assump_60


variable (p7 p1 p6 p4 p3 p2 : Prop)
theorem file2_46386 : ((((((p2 → False) → (p1 → p4)) → ((p2 ∨ p3) → (p6 → False))) ∧ (((False → False) → (p1 ∨ p6)) → False)) ∧ ((((False ∧ p1) → (False ∧ p7)) ∨ ((p6 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_25 : (((False ∧ p1) → (False ∧ p7)) ∨ ((p6 → False) → False)) := by
        apply Or.inl
        intro assump_13
        apply And.intro
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
        cases assump_13
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
      let assump_12 := assump_3 assump_25
      apply False.elim assump_12


variable (p7 p4 p0 p2 p1 p5 : Prop)
theorem file2_47194 : ((((((True ∨ False) ∨ (True → p5)) ∨ ((p2 ∧ p1) → (p5 → False))) ∧ (((p7 → False) → (True ∨ False)) ∧ ((p0 → False) → (p0 → p4)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((True ∨ False) ∨ (True → p5)) ∨ ((p2 ∧ p1) → (p5 → False))) ∧ (((p7 → False) → (True ∨ False)) ∧ ((p0 → False) → (p0 → p4)))) := by
    apply And.intro
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
    apply And.intro
    intro assump_5
    apply Or.inl
    apply True.intro
    intro assump_8
    intro assump_9
    have assump_22 : p0 := by
      exact assump_9
    let assump_14 := assump_8 assump_22
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p4 p5 p1 p0 p6 p7 p3 : Prop)
theorem file2_47977 : (((((p1 ∨ p7) ∧ (p1 → p7)) → ((p0 → False) → (p0 → False))) ∨ (((p1 → p3) → (p1 → False)) ∨ ((p0 ∧ p4) → (p0 → p0)))) ∨ ((((p6 ∨ p7) → False) ∧ ((p3 ∨ p0) ∨ (p0 → p0))) ∨ (((True ∨ p0) ∧ (p5 ∨ p7)) ∧ ((p6 ∧ p1) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      have assump_33 : p0 := by
        exact assump_3
      let assump_19 := assump_2 assump_33
      apply False.elim assump_19
    case inr assump_11 =>
      have assump_34 : p0 := by
        exact assump_3
      let assump_29 := assump_2 assump_34
      apply False.elim assump_29


variable (p7 p3 p1 p2 p6 : Prop)
theorem file2_48726 : (((((p2 ∨ True) ∨ (p1 → False)) → False) → (((p6 ∧ p3) → False) → False)) ∨ ((((p7 ∧ p3) ∧ (p6 ∨ p2)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : ((p2 ∨ True) ∨ (p1 → False)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p2 p5 p7 p6 p1 p3 p0 : Prop)
theorem file2_49139 : (((((p7 → p6) → False) ∧ ((p2 → p2) ∧ (False ∨ p1))) ∨ (((p1 → False) ∧ (p2 ∧ p1)) → False)) → ((((p1 → p5) → False) → ((p6 → False) ∧ (p3 → False))) → (((p0 ∨ p1) → False) → ((p7 → p7) ∧ (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_1
  case inl assump_11 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_14
      case intro assump_17 assump_18 =>
        cases assump_18
        case inl assump_21 =>
          apply False.elim assump_21
        case inr assump_22 =>
          exact assump_4
  case inr assump_12 =>
    exact assump_4
  intro assump_29
  apply False.elim assump_29


variable (p5 p7 p6 p2 p1 p4 p3 : Prop)
theorem file2_49899 : (((((p2 ∧ p7) → False) → ((p7 ∨ p3) → (p4 ∨ p5))) → False) → ((((p6 → False) ∨ (True → False)) → False) → (((p4 ∧ False) → (p6 ∧ p1)) ∨ ((p3 ∧ p1) → (p7 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply And.intro
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_9
  cases assump_7
  case intro assump_14 assump_15 =>
    apply False.elim assump_15


variable (p5 p0 p3 p2 p6 p7 p1 : Prop)
theorem file2_50383 : (((((p0 ∨ True) → False) → False) → False) → ((((p7 ∨ p0) ∨ (p3 ∧ p1)) → ((True → False) ∧ (p0 ∨ p2))) ∧ (((p5 ∨ p1) ∨ (False → False)) → ((p6 ∧ True) ∧ (p1 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      have assump_203 : (((p0 ∨ True) → False) → False) := by
        intro assump_15
        have assump_204 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_18 := assump_15 assump_204
        apply False.elim assump_18
      let assump_14 := assump_1 assump_203
      apply False.elim assump_14
    case inr assump_9 =>
      have assump_205 : (((p0 ∨ True) → False) → False) := by
        intro assump_30
        have assump_206 : (p0 ∨ True) := by
          apply Or.inl
          exact assump_9
        let assump_33 := assump_30 assump_206
        apply False.elim assump_33
      let assump_29 := assump_1 assump_205
      apply False.elim assump_29
  case inr assump_7 =>
    cases assump_7
    case intro assump_40 assump_41 =>
      have assump_207 : (((p0 ∨ True) → False) → False) := by
        intro assump_49
        have assump_208 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_52 := assump_49 assump_208
        apply False.elim assump_52
      let assump_48 := assump_1 assump_207
      apply False.elim assump_48
  cases assump_2
  case inl assump_59 =>
    cases assump_59
    case inl assump_61 =>
      have assump_209 : (((p0 ∨ True) → False) → False) := by
        intro assump_68
        have assump_210 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_71 := assump_68 assump_210
        apply False.elim assump_71
      let assump_67 := assump_1 assump_209
      apply False.elim assump_67
    case inr assump_62 =>
      apply Or.inl
      exact assump_62
  case inr assump_60 =>
    cases assump_60
    case intro assump_82 assump_83 =>
      have assump_211 : (((p0 ∨ True) → False) → False) := by
        intro assump_91
        have assump_212 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_94 := assump_91 assump_212
        apply False.elim assump_94
      let assump_90 := assump_1 assump_211
      apply False.elim assump_90
  intro assump_101
  apply And.intro
  apply And.intro
  cases assump_101
  case inl assump_102 =>
    cases assump_102
    case inl assump_104 =>
      have assump_213 : (((p0 ∨ True) → False) → False) := by
        intro assump_111
        have assump_214 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_114 := assump_111 assump_214
        apply False.elim assump_114
      let assump_110 := assump_1 assump_213
      apply False.elim assump_110
    case inr assump_105 =>
      have assump_215 : (((p0 ∨ True) → False) → False) := by
        intro assump_126
        have assump_216 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_129 := assump_126 assump_216
        apply False.elim assump_129
      let assump_125 := assump_1 assump_215
      apply False.elim assump_125
  case inr assump_103 =>
    have assump_217 : (((p0 ∨ True) → False) → False) := by
      intro assump_141
      have assump_218 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_144 := assump_141 assump_218
      apply False.elim assump_144
    let assump_140 := assump_1 assump_217
    apply False.elim assump_140
  apply True.intro
  intro assump_151
  cases assump_101
  case inl assump_154 =>
    cases assump_154
    case inl assump_156 =>
      have assump_219 : (((p0 ∨ True) → False) → False) := by
        intro assump_163
        have assump_220 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_166 := assump_163 assump_220
        apply False.elim assump_166
      let assump_162 := assump_1 assump_219
      apply False.elim assump_162
    case inr assump_157 =>
      have assump_221 : (((p0 ∨ True) → False) → False) := by
        intro assump_178
        have assump_222 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_181 := assump_178 assump_222
        apply False.elim assump_181
      let assump_177 := assump_1 assump_221
      apply False.elim assump_177
  case inr assump_155 =>
    have assump_223 : (((p0 ∨ True) → False) → False) := by
      intro assump_193
      have assump_224 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_196 := assump_193 assump_224
      apply False.elim assump_196
    let assump_192 := assump_1 assump_223
    apply False.elim assump_192


variable (p4 p3 p6 p5 p2 p1 p7 : Prop)
theorem file2_55220 : (((((p6 ∧ p5) ∧ (p2 ∧ p3)) ∧ ((p5 ∧ p1) ∧ (p4 ∨ p2))) ∧ (((p2 → p4) ∧ (p2 ∨ p1)) ∧ ((False ∨ False) ∧ (p7 → p3)))) → False) := by
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
            cases assump_5
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_21
                case inl assump_28 =>
                  cases assump_3
                  case intro assump_32 assump_33 =>
                    cases assump_32
                    case intro assump_34 assump_35 =>
                      cases assump_35
                      case inl assump_38 =>
                        cases assump_33
                        case intro assump_42 assump_43 =>
                          cases assump_42
                          case inl assump_44 =>
                            apply False.elim assump_44
                          case inr assump_45 =>
                            apply False.elim assump_45
                      case inr assump_39 =>
                        cases assump_33
                        case intro assump_52 assump_53 =>
                          cases assump_52
                          case inl assump_54 =>
                            apply False.elim assump_54
                          case inr assump_55 =>
                            apply False.elim assump_55
                case inr assump_29 =>
                  cases assump_3
                  case intro assump_62 assump_63 =>
                    cases assump_62
                    case intro assump_64 assump_65 =>
                      cases assump_65
                      case inl assump_68 =>
                        cases assump_63
                        case intro assump_72 assump_73 =>
                          cases assump_72
                          case inl assump_74 =>
                            apply False.elim assump_74
                          case inr assump_75 =>
                            apply False.elim assump_75
                      case inr assump_69 =>
                        cases assump_63
                        case intro assump_82 assump_83 =>
                          cases assump_82
                          case inl assump_84 =>
                            apply False.elim assump_84
                          case inr assump_85 =>
                            apply False.elim assump_85


variable (p4 p5 p7 p1 p6 p0 p3 : Prop)
theorem file2_57972 : ((((((p3 ∧ p6) ∧ (True ∨ p5)) → ((p1 ∨ p4) → (p3 ∨ p3))) ∧ (((p7 ∧ False) → (p0 ∧ p6)) ∨ ((p0 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_57 : ((((p3 ∧ p6) ∧ (True ∨ p5)) → ((p1 ∨ p4) → (p3 ∨ p3))) ∧ (((p7 ∧ False) → (p0 ∧ p6)) ∨ ((p0 → False) → False))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case inl assump_19 =>
            apply Or.inl
            exact assump_13
          case inr assump_20 =>
            apply Or.inl
            exact assump_13
    case inr assump_8 =>
      cases assump_5
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_28
          case inl assump_35 =>
            apply Or.inl
            exact assump_29
          case inr assump_36 =>
            apply Or.inl
            exact assump_29
    apply Or.inl
    intro assump_41
    apply And.intro
    cases assump_41
    case intro assump_42 assump_43 =>
      apply False.elim assump_43
    cases assump_41
    case intro assump_48 assump_49 =>
      apply False.elim assump_49
  let assump_4 := assump_1 assump_57
  apply False.elim assump_4


variable (p3 p5 p1 p0 p4 p7 : Prop)
theorem file2_59401 : ((((((False → False) → (p0 → False)) ∨ ((p7 ∨ p1) → (p4 → False))) → (((False ∧ p3) → (p1 ∨ False)) ∧ ((True ∨ p5) ∨ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False → False) → (p0 → False)) ∨ ((p7 ∨ p1) → (p4 → False))) → (((False ∧ p3) → (p1 ∨ False)) ∧ ((True ∨ p5) ∨ (p1 → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
    cases assump_5
    case inl assump_11 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_12 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p7 p4 p2 p6 p5 p0 p1 p3 : Prop)
theorem file2_60200 : ((((((p5 ∧ p2) ∧ (p6 → p7)) ∧ ((p7 → p1) → (p6 → False))) → (((p4 ∧ p4) ∨ (p7 ∨ p3)) ∧ ((p4 → p2) → (p7 → p3)))) ∧ ((((False ∧ True) → (True → p1)) ∧ ((p5 ∨ p3) → (p0 → p0))) → False)) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    have assump_39 : (((False ∧ True) → (True → p1)) ∧ ((p5 ∨ p3) → (p0 → p0))) := by
      apply And.intro
      intro assump_18
      intro assump_19
      cases assump_18
      case intro assump_22 assump_23 =>
        apply False.elim assump_22
      intro assump_26
      intro assump_27
      cases assump_26
      case inl assump_30 =>
        exact assump_27
      case inr assump_31 =>
        exact assump_27
    let assump_17 := assump_12 assump_39
    apply False.elim assump_17


variable (p2 p6 p4 p1 p7 p0 p5 : Prop)
theorem file2_61026 : (((((p2 ∧ p0) → (p5 → False)) ∧ ((p4 ∨ p4) → False)) ∨ (((p1 ∧ p5) ∨ (p1 → False)) → ((p4 ∧ True) → False))) → ((((p0 ∧ p6) ∨ (p0 ∧ p6)) → ((p0 ∨ p1) → (p4 → False))) → (((p7 → False) ∧ (True ∨ p1)) → ((p1 ∧ False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p7 p1 : Prop)
theorem file2_61456 : ((((((True → False) → (p1 ∨ p7)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((True → False) → (p1 ∨ p7)) → False) → False) := by
    intro assump_5
    have assump_23 : ((True → False) → (p1 ∨ p7)) := by
      intro assump_9
      have assump_24 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_24
      apply False.elim assump_12
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p5 p3 p0 p6 p2 p7 : Prop)
theorem file2_62046 : (((((p0 ∨ False) → (True → True)) ∨ ((p3 ∧ True) ∨ (p3 → False))) ∨ (((p3 → False) → False) ∨ ((p7 ∧ True) ∧ (p0 ∧ True)))) ∨ ((((p2 ∧ p5) ∨ (p5 ∨ True)) ∨ ((p5 → p5) ∧ (p2 ∧ p6))) → (((True → False) → False) → ((p6 ∧ p7) ∧ (False → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply True.intro


variable (p3 p0 p5 : Prop)
theorem file2_62445 : (((((False → True) ∧ (p5 → False)) → False) → False) → ((((p0 ∧ False) ∨ (False ∧ p0)) ∧ ((p3 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8
    case inr assump_6 =>
      cases assump_6
      case intro assump_13 assump_14 =>
        apply False.elim assump_13


variable (p0 p3 p7 p4 p6 p5 : Prop)
theorem file2_62977 : (((((True → False) ∧ (p3 ∧ p0)) → False) → False) → ((((p5 → p4) ∧ (p5 ∧ False)) ∨ ((p5 → False) ∧ (p5 → p4))) ∨ (((p4 ∧ p6) → (True ∨ p7)) → ((True → p7) → (p0 ∧ p3))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply And.intro
  intro assump_29
  have assump_79 : (((True → False) ∧ (p3 ∧ p0)) → False) := by
    intro assump_34
    cases assump_34
    case intro assump_35 assump_36 =>
      cases assump_36
      case intro assump_39 assump_40 =>
        have assump_80 : True := by
          apply True.intro
        let assump_47 := assump_35 assump_80
        apply False.elim assump_47
  let assump_33 := assump_1 assump_79
  apply False.elim assump_33
  intro assump_54
  have assump_81 : (((True → False) ∧ (p3 ∧ p0)) → False) := by
    intro assump_59
    cases assump_59
    case intro assump_60 assump_61 =>
      cases assump_61
      case intro assump_64 assump_65 =>
        have assump_82 : True := by
          apply True.intro
        let assump_72 := assump_60 assump_82
        apply False.elim assump_72
  let assump_58 := assump_1 assump_81
  apply False.elim assump_58


variable (p0 p4 p5 p6 : Prop)
theorem file2_64137 : (((((p5 ∨ p0) → False) ∧ ((p4 → True) → False)) → False) ∨ ((((p0 → False) → False) → False) ∨ (((p4 ∧ p4) ∧ (p5 → p6)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (p4 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p4 p5 : Prop)
theorem file2_64557 : ((((((True → False) ∧ (p5 ∧ p4)) ∨ ((p5 → p5) → False)) → False) → False) → False) := by
  intro assump_7
  have assump_42 : ((((True → False) ∧ (p5 ∧ p4)) ∨ ((p5 → p5) → False)) → False) := by
    intro assump_11
    cases assump_11
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          have assump_43 : True := by
            apply True.intro
          let assump_26 := assump_14 assump_43
          apply False.elim assump_26
    case inr assump_13 =>
      have assump_44 : (p5 → p5) := by
        intro assump_33
        exact assump_33
      let assump_32 := assump_13 assump_44
      apply False.elim assump_32
  let assump_10 := assump_7 assump_42
  apply False.elim assump_10


variable (p6 p7 p1 p5 p0 p3 p4 : Prop)
theorem file2_65415 : ((((((p6 ∨ p5) → (p1 → p3)) → ((True → True) → (p4 → False))) ∧ (((p0 → False) → (p4 ∧ p5)) ∨ ((True ∨ p6) ∧ (p0 ∧ p7)))) ∧ ((((True → p0) ∨ (p5 ∧ p0)) → False) ∧ (((p6 ∧ p6) → (True ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          have assump_83 : ((p6 ∧ p6) → (True ∨ p0)) := by
            intro assump_19
            cases assump_19
            case intro assump_20 assump_21 =>
              apply Or.inl
              apply True.intro
          let assump_18 := assump_13 assump_83
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case intro assump_29 assump_30 =>
          cases assump_29
          case inl assump_31 =>
            cases assump_30
            case intro assump_35 assump_36 =>
              cases assump_3
              case intro assump_41 assump_42 =>
                have assump_84 : ((p6 ∧ p6) → (True ∨ p0)) := by
                  intro assump_48
                  cases assump_48
                  case intro assump_49 assump_50 =>
                    apply Or.inl
                    apply True.intro
                let assump_47 := assump_42 assump_84
                apply False.elim assump_47
          case inr assump_32 =>
            cases assump_30
            case intro assump_60 assump_61 =>
              cases assump_3
              case intro assump_66 assump_67 =>
                have assump_85 : ((p6 ∧ p6) → (True ∨ p0)) := by
                  intro assump_73
                  cases assump_73
                  case intro assump_74 assump_75 =>
                    apply Or.inl
                    apply True.intro
                let assump_72 := assump_67 assump_85
                apply False.elim assump_72


variable (p3 p1 p0 p2 p5 p6 : Prop)
theorem file2_67416 : ((((((p2 ∧ False) ∧ (p3 ∨ p1)) ∧ ((p0 → False) ∧ (p6 → False))) → (((True → False) → False) ∨ ((p6 ∧ p0) ∨ (p5 ∨ False)))) → False) → False) := by
  intro assump_5
  have assump_23 : ((((p2 ∧ False) ∧ (p3 ∨ p1)) ∧ ((p0 → False) ∧ (p6 → False))) → (((True → False) → False) ∨ ((p6 ∧ p0) ∨ (p5 ∨ False)))) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  let assump_8 := assump_5 assump_23
  apply False.elim assump_8


variable (p3 p1 p0 : Prop)
theorem file2_68083 : (((((p0 → p1) → False) → ((True ∧ p3) → (p1 → False))) → False) → False) := by
  intro assump_1
  have assump_28 : (((p0 → p1) → False) → ((True ∧ p3) → (p1 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      have assump_29 : (p0 → p1) := by
        intro assump_19
        exact assump_7
      let assump_18 := assump_5 assump_29
      apply False.elim assump_18
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p5 p3 p7 p1 p2 p0 p6 p4 : Prop)
theorem file2_68663 : (((((p3 → p1) ∧ (p3 ∧ p5)) → ((p5 → p0) → (p7 ∧ p5))) ∧ (((True → False) → False) → False)) → ((((p0 ∧ p2) → False) ∨ ((p4 → False) → (p6 → False))) → (((p4 ∧ p0) ∨ (p2 → p6)) → ((p4 → p1) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_2
      case inl assump_15 =>
        cases assump_1
        case intro assump_19 assump_20 =>
          have assump_97 : ((True → False) → False) := by
            intro assump_26
            have assump_98 : True := by
              apply True.intro
            let assump_29 := assump_26 assump_98
            apply False.elim assump_29
          let assump_25 := assump_20 assump_97
          apply False.elim assump_25
      case inr assump_16 =>
        cases assump_1
        case intro assump_38 assump_39 =>
          have assump_99 : ((True → False) → False) := by
            intro assump_45
            have assump_100 : True := by
              apply True.intro
            let assump_48 := assump_45 assump_100
            apply False.elim assump_48
          let assump_44 := assump_39 assump_99
          apply False.elim assump_44
  case inr assump_8 =>
    cases assump_2
    case inl assump_57 =>
      cases assump_1
      case intro assump_61 assump_62 =>
        have assump_101 : ((True → False) → False) := by
          intro assump_68
          have assump_102 : True := by
            apply True.intro
          let assump_71 := assump_68 assump_102
          apply False.elim assump_71
        let assump_67 := assump_62 assump_101
        apply False.elim assump_67
    case inr assump_58 =>
      cases assump_1
      case intro assump_80 assump_81 =>
        have assump_103 : ((True → False) → False) := by
          intro assump_87
          have assump_104 : True := by
            apply True.intro
          let assump_90 := assump_87 assump_104
          apply False.elim assump_90
        let assump_86 := assump_81 assump_103
        apply False.elim assump_86


variable (p3 p0 p4 : Prop)
theorem file2_70802 : ((((((p3 → p4) → (p4 → False)) → False) → (((True ∧ True) → (p4 ∨ True)) ∨ ((p3 ∨ False) → (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 → p4) → (p4 → False)) → False) → (((True ∧ True) → (p4 ∨ True)) ∨ ((p3 ∨ False) → (p0 → False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p4 p3 p6 p7 p2 : Prop)
theorem file2_71358 : ((((((p3 ∧ p7) ∧ (p4 ∧ p7)) → ((p3 ∨ p4) ∧ (p3 ∨ p3))) ∧ (((p2 ∨ p6) ∧ (p7 → False)) → False)) ∧ ((((p6 ∨ p4) → False) ∧ ((p1 ∨ p3) ∧ (p7 ∧ p4))) ∧ (((p1 ∧ p7) ∧ (True → p4)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_17
              case intro assump_22 assump_23 =>
                have assump_55 : ((p1 ∧ p7) ∧ (True → p4)) := by
                  apply And.intro
                  apply And.intro
                  exact assump_18
                  exact assump_22
                  intro assump_31
                  exact assump_23
                let assump_30 := assump_11 assump_55
                apply False.elim assump_30
            case inr assump_19 =>
              cases assump_17
              case intro assump_39 assump_40 =>
                have assump_56 : (p6 ∨ p4) := by
                  apply Or.inr
                  exact assump_40
                let assump_51 := assump_12 assump_56
                apply False.elim assump_51


variable (p2 p5 p0 : Prop)
theorem file2_72757 : ((((((False ∧ p2) → (False → p0)) → False) → (((p5 → p0) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False ∧ p2) → (False → p0)) → False) → (((p5 → p0) → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_23 : ((False ∧ p2) → (False → p0)) := by
      intro assump_12
      intro assump_13
      apply False.elim assump_13
    let assump_11 := assump_5 assump_23
    apply False.elim assump_11
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p3 p1 p4 p0 p5 p6 : Prop)
theorem file2_73344 : (((((False ∨ p0) ∨ (p0 → False)) → ((p5 → False) → (p2 → p3))) → (((p5 → False) ∧ (p5 ∧ p5)) → ((False ∧ p3) → False))) → ((((True ∨ p6) → (True → False)) ∧ ((p1 → p6) → False)) → (((p4 ∧ p6) → (p4 → False)) → ((p4 ∧ p0) → (p3 ∨ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_2
    case intro assump_13 assump_14 =>
      apply Or.inr
      exact assump_5


variable (p2 p0 p4 p7 p5 p3 p6 : Prop)
theorem file2_73866 : ((((((p2 ∨ p6) → (p5 ∨ False)) → ((p3 ∨ p3) → False)) → (((p0 → False) ∧ (p4 → p3)) ∨ ((p7 ∧ True) ∨ (p0 ∨ False)))) ∧ ((((False → False) → (p2 → False)) → ((True ∧ p2) ∧ (p2 ∨ p4))) ∧ (((p5 ∨ p7) ∨ (p7 ∨ p0)) ∧ ((True ∨ p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            have assump_50 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_20 := assump_11 assump_50
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_51 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_28 := assump_11 assump_51
            apply False.elim assump_28
        case inr assump_13 =>
          cases assump_13
          case inl assump_32 =>
            have assump_52 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_38 := assump_11 assump_52
            apply False.elim assump_38
          case inr assump_33 =>
            have assump_53 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_46 := assump_11 assump_53
            apply False.elim assump_46


variable (p2 p3 p0 p7 p6 p1 p5 : Prop)
theorem file2_75401 : ((((((p2 → False) ∧ (p7 → p2)) → ((p0 ∨ p1) → False)) → (((p5 ∧ False) → (p6 ∨ p2)) ∨ ((p6 ∨ True) → (p7 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 → False) ∧ (p7 → p2)) → ((p0 ∨ p1) → False)) → (((p5 ∧ False) → (p6 ∨ p2)) ∨ ((p6 ∨ True) → (p7 ∨ p3)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p5 p4 p1 p6 p2 p3 : Prop)
theorem file2_75965 : ((((((p1 ∨ p0) → False) → ((True ∨ False) ∧ (p1 → p5))) ∨ (((p3 → p2) ∨ (p4 ∨ p4)) → ((p3 ∧ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p1 ∨ p0) → False) → ((True ∨ False) ∧ (p1 → p5))) ∨ (((p3 → p2) ∨ (p4 ∨ p4)) → ((p3 ∧ p6) → False))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_8
    have assump_21 : (p1 ∨ p0) := by
      apply Or.inl
      exact assump_8
    let assump_13 := assump_5 assump_21
    apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p6 p7 p5 p3 p0 p4 p2 p1 : Prop)
theorem file2_76635 : (((((p1 → p7) ∧ (p0 → False)) → False) → (((p0 ∨ p5) → False) → False)) → ((((False → False) → False) → ((p3 ∧ True) ∨ (False ∧ p2))) ∨ (((p6 ∧ p3) → (True ∨ p4)) ∨ ((p0 → False) ∧ (p3 ∨ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (False → False) := by
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p1 p7 p6 p2 p4 : Prop)
theorem file2_77100 : ((((((p2 ∨ False) → (p1 → p7)) → ((True → False) → (p7 ∧ p4))) ∨ (((p6 ∧ p1) → (p7 ∧ False)) ∧ ((p1 ∨ p1) ∧ (p7 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p2 ∨ False) → (p1 → p7)) → ((True → False) → (p7 ∧ p4))) ∨ (((p6 ∧ p1) → (p7 ∧ False)) ∧ ((p1 ∨ p1) ∧ (p7 ∧ False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply And.intro
    have assump_29 : True := by
      apply True.intro
    let assump_12 := assump_6 assump_29
    apply False.elim assump_12
    have assump_30 : True := by
      apply True.intro
    let assump_21 := assump_6 assump_30
    apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p4 p5 p3 p2 p1 p6 : Prop)
theorem file2_77864 : (((((p4 → p4) → False) → ((p3 → p2) → (False → False))) → (((p4 → False) ∨ (p5 → p2)) ∧ ((p3 ∧ p6) ∧ (p6 → p6)))) → ((((p5 ∨ p3) → (p1 → False)) → False) → (((False → False) → (p1 → True)) ∧ ((False ∨ p5) ∨ (False → False))))) := by
  intro assump_5
  intro assump_6
  apply And.intro
  intro assump_7
  intro assump_8
  apply True.intro
  apply Or.inr
  intro assump_13
  apply False.elim assump_13


variable (p6 p1 p5 p3 p4 p7 p2 : Prop)
theorem file2_78327 : (((((p3 ∧ False) ∧ (p1 → True)) ∨ ((p3 ∨ p7) ∧ (True → False))) ∧ (((p7 ∨ p1) ∧ (p6 → False)) ∧ ((p2 → True) → False))) → ((((p5 ∨ p2) ∨ (p7 → False)) ∧ ((p7 ∧ p6) → (p1 ∧ p4))) → (((True ∧ False) ∧ (p2 → False)) → ((p1 ∨ p5) ∨ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p7 p2 p1 p3 : Prop)
theorem file2_78821 : (((((p1 → False) ∧ (False ∧ p7)) → ((p3 ∨ p2) → False)) → False) → False) := by
  intro assump_1
  have assump_32 : (((p1 → False) ∧ (False ∧ p7)) → ((p3 ∨ p2) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
    case inr assump_8 =>
      cases assump_5
      case intro assump_21 assump_22 =>
        cases assump_22
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p2 p6 p3 p0 p5 p1 : Prop)
theorem file2_79557 : (((((False → False) → (p2 ∧ p1)) ∨ ((False ∨ p3) ∧ (p0 ∨ p1))) → (((p1 ∧ p0) → False) ∧ ((p2 ∨ False) → (False ∧ False)))) → ((((False → False) → False) → ((p1 ∧ p1) → (p0 → p1))) → (((p5 → p3) → (True ∨ p0)) ∨ ((False ∨ p6) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply Or.inl
  apply True.intro


variable (p4 p0 p3 p7 p5 p2 : Prop)
theorem file2_79960 : (((((p0 → False) ∧ (p7 ∧ p0)) → False) ∨ (((True → False) → (p3 ∧ p3)) → False)) ∨ ((((p7 ∨ p3) → (False ∧ p4)) ∧ ((p2 ∧ p3) ∨ (p5 → False))) ∨ (((p0 ∨ p0) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_18 : p0 := by
        exact assump_7
      let assump_14 := assump_2 assump_18
      apply False.elim assump_14


variable (p1 p2 p7 p6 p0 p5 p4 p3 : Prop)
theorem file2_80491 : (((((p3 ∧ p1) ∨ (p1 → False)) ∧ ((False ∨ p3) → (True → p4))) ∧ (((p3 → False) → (p2 ∨ p3)) ∧ ((p1 → p7) → (p6 → False)))) → ((((p5 ∨ True) ∧ (p4 ∨ False)) → ((p0 ∨ p6) ∨ (False → True))) ∨ (((p3 → False) → False) → ((p5 → p3) → (p5 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            apply Or.inl
            intro assump_22
            cases assump_22
            case intro assump_23 assump_24 =>
              cases assump_23
              case inl assump_25 =>
                cases assump_24
                case inl assump_29 =>
                  apply Or.inr
                  intro assump_33
                  apply True.intro
                case inr assump_30 =>
                  apply False.elim assump_30
              case inr assump_26 =>
                cases assump_24
                case inl assump_38 =>
                  apply Or.inr
                  intro assump_42
                  apply True.intro
                case inr assump_39 =>
                  apply False.elim assump_39
      case inr assump_7 =>
        cases assump_3
        case intro assump_49 assump_50 =>
          apply Or.inl
          intro assump_55
          cases assump_55
          case intro assump_56 assump_57 =>
            cases assump_56
            case inl assump_58 =>
              cases assump_57
              case inl assump_62 =>
                apply Or.inr
                intro assump_66
                apply True.intro
              case inr assump_63 =>
                apply False.elim assump_63
            case inr assump_59 =>
              cases assump_57
              case inl assump_71 =>
                apply Or.inr
                intro assump_75
                apply True.intro
              case inr assump_72 =>
                apply False.elim assump_72


variable (p1 p4 p0 p7 p2 p3 : Prop)
theorem file2_82626 : ((((((True → False) ∨ (True → False)) ∨ ((p7 → False) → False)) ∨ (((p4 → p2) → False) → False)) ∧ ((((p3 → p2) ∧ (p7 ∧ p0)) → ((p7 ∨ p4) ∨ (p3 ∨ p1))) → False)) → False) := by
  intro assump_37
  cases assump_37
  case intro assump_38 assump_39 =>
    cases assump_38
    case inl assump_40 =>
      cases assump_40
      case inl assump_42 =>
        cases assump_42
        case inl assump_44 =>
          have assump_122 : (((p3 → p2) ∧ (p7 ∧ p0)) → ((p7 ∨ p4) ∨ (p3 ∨ p1))) := by
            intro assump_51
            cases assump_51
            case intro assump_52 assump_53 =>
              cases assump_53
              case intro assump_56 assump_57 =>
                apply Or.inl
                apply Or.inl
                exact assump_56
          let assump_50 := assump_39 assump_122
          apply False.elim assump_50
        case inr assump_45 =>
          have assump_123 : (((p3 → p2) ∧ (p7 ∧ p0)) → ((p7 ∨ p4) ∨ (p3 ∨ p1))) := by
            intro assump_70
            cases assump_70
            case intro assump_71 assump_72 =>
              cases assump_72
              case intro assump_75 assump_76 =>
                apply Or.inl
                apply Or.inl
                exact assump_75
          let assump_69 := assump_39 assump_123
          apply False.elim assump_69
      case inr assump_43 =>
        have assump_124 : (((p3 → p2) ∧ (p7 ∧ p0)) → ((p7 ∨ p4) ∨ (p3 ∨ p1))) := by
          intro assump_89
          cases assump_89
          case intro assump_90 assump_91 =>
            cases assump_91
            case intro assump_94 assump_95 =>
              apply Or.inl
              apply Or.inl
              exact assump_94
        let assump_88 := assump_39 assump_124
        apply False.elim assump_88
    case inr assump_41 =>
      have assump_125 : (((p3 → p2) ∧ (p7 ∧ p0)) → ((p7 ∨ p4) ∨ (p3 ∨ p1))) := by
        intro assump_108
        cases assump_108
        case intro assump_109 assump_110 =>
          cases assump_110
          case intro assump_113 assump_114 =>
            apply Or.inl
            apply Or.inl
            exact assump_113
      let assump_107 := assump_39 assump_125
      apply False.elim assump_107


variable (p4 p3 p2 p5 p6 p1 p7 : Prop)
theorem file2_84880 : (((((p6 ∨ p2) ∨ (p1 → False)) → False) → (((p6 → p7) → (p5 → p1)) → ((True → False) ∧ (p3 ∨ p4)))) → ((((p7 ∨ p6) → False) → False) → (((p7 ∨ p1) → False) → ((False ∧ p3) → False)))) := by
  intro assump_14
  intro assump_15
  intro assump_16
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    apply False.elim assump_18


variable (p0 p4 p7 p1 p3 p5 p2 : Prop)
theorem file2_85289 : (((((True ∨ True) → False) → ((p2 → p1) ∧ (p3 ∧ p4))) ∨ (((p1 → False) → (p0 → p5)) → ((True → False) ∧ (p7 → False)))) ∧ ((((False ∧ p0) ∧ (p5 → p4)) → False) ∨ (((False → False) → False) → ((p4 → p1) → (p1 ∨ p2))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_30 : (True ∨ True) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_30
  apply False.elim assump_7
  apply And.intro
  have assump_31 : (True ∨ True) := by
    apply Or.inl
    apply True.intro
  let assump_13 := assump_1 assump_31
  apply False.elim assump_13
  have assump_32 : (True ∨ True) := by
    apply Or.inl
    apply True.intro
  let assump_19 := assump_1 assump_32
  apply False.elim assump_19
  apply Or.inl
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    cases assump_24
    case intro assump_26 assump_27 =>
      apply False.elim assump_26


variable (p5 p6 p3 p0 p7 p2 : Prop)
theorem file2_86284 : ((((((False ∨ p3) ∨ (p2 → p6)) → False) → False) ∧ ((((p7 → p5) → (p3 ∨ p0)) → False) ∧ (((p5 ∨ p2) ∧ (p2 → False)) ∧ ((p7 → False) ∧ (p2 ∧ True))))) → False) := by
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
          case inl assump_14 =>
            cases assump_11
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                have assump_56 : p2 := by
                  exact assump_24
                let assump_32 := assump_13 assump_56
                apply False.elim assump_32
          case inr assump_15 =>
            cases assump_11
            case intro assump_40 assump_41 =>
              cases assump_41
              case intro assump_44 assump_45 =>
                have assump_57 : p2 := by
                  exact assump_44
                let assump_52 := assump_13 assump_57
                apply False.elim assump_52


variable (p6 p4 p2 p7 p1 p5 p3 : Prop)
theorem file2_87500 : ((((((p7 ∧ p4) → (p3 ∨ p7)) → False) → (((p6 → False) → (p5 ∨ False)) → ((p4 ∧ True) → (True ∧ p1)))) → ((((True → p5) → (True ∨ p2)) ∨ ((p6 ∨ p4) ∨ (p1 ∧ True))) → False)) → False) := by
  intro assump_19
  have assump_54 : ((((p7 ∧ p4) → (p3 ∨ p7)) → False) → (((p6 → False) → (p5 ∨ False)) → ((p4 ∧ True) → (True ∧ p1)))) := by
    intro assump_23
    intro assump_24
    intro assump_25
    apply And.intro
    apply True.intro
    cases assump_25
    case intro assump_26 assump_27 =>
      have assump_55 : ((p7 ∧ p4) → (p3 ∨ p7)) := by
        intro assump_37
        cases assump_37
        case intro assump_38 assump_39 =>
          apply Or.inr
          exact assump_38
      let assump_36 := assump_23 assump_55
      apply False.elim assump_36
  let assump_22 := assump_19 assump_54
  have assump_56 : (((True → p5) → (True ∨ p2)) ∨ ((p6 ∨ p4) ∨ (p1 ∧ True))) := by
    apply Or.inl
    intro assump_48
    apply Or.inl
    apply True.intro
  let assump_47 := assump_22 assump_56
  apply False.elim assump_47


variable (p0 p2 p5 p3 p6 : Prop)
theorem file2_88580 : ((((((False ∧ p5) → (p6 ∨ True)) ∨ ((True ∧ p3) → False)) ∨ (((True → False) ∨ (p3 ∧ p0)) ∨ ((p2 → p0) ∧ (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p5) → (p6 ∨ True)) ∨ ((True ∧ p3) → False)) ∨ (((True → False) ∨ (p3 ∧ p0)) ∨ ((p2 → p0) ∧ (p6 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p3 p2 p6 p4 p0 p1 : Prop)
theorem file2_89154 : (((((False → p6) → False) ∨ ((p1 ∨ p2) → False)) ∧ (((False → False) ∨ (True ∨ False)) ∧ ((True ∨ p6) → False))) → ((((True ∧ False) ∧ (True → False)) ∨ ((False → False) → False)) ∧ (((p1 ∧ p4) ∧ (p5 → False)) → ((p0 ∨ p3) ∨ (p4 ∧ p4))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inr
          intro assump_16
          have assump_125 : (True ∨ p6) := by
            apply Or.inl
            apply True.intro
          let assump_20 := assump_9 assump_125
          apply False.elim assump_20
        case inr assump_11 =>
          cases assump_11
          case inl assump_24 =>
            apply Or.inr
            intro assump_30
            have assump_126 : (True ∨ p6) := by
              apply Or.inl
              apply True.intro
            let assump_34 := assump_9 assump_126
            apply False.elim assump_34
          case inr assump_25 =>
            apply False.elim assump_25
    case inr assump_5 =>
      cases assump_3
      case intro assump_42 assump_43 =>
        cases assump_42
        case inl assump_44 =>
          apply Or.inr
          intro assump_50
          have assump_127 : (True ∨ p6) := by
            apply Or.inl
            apply True.intro
          let assump_54 := assump_43 assump_127
          apply False.elim assump_54
        case inr assump_45 =>
          cases assump_45
          case inl assump_58 =>
            apply Or.inr
            intro assump_64
            have assump_128 : (True ∨ p6) := by
              apply Or.inl
              apply True.intro
            let assump_68 := assump_43 assump_128
            apply False.elim assump_68
          case inr assump_59 =>
            apply False.elim assump_59
  intro assump_74
  cases assump_74
  case intro assump_75 assump_76 =>
    cases assump_75
    case intro assump_77 assump_78 =>
      cases assump_1
      case intro assump_85 assump_86 =>
        cases assump_85
        case inl assump_87 =>
          cases assump_86
          case intro assump_91 assump_92 =>
            cases assump_91
            case inl assump_93 =>
              apply Or.inr
              apply And.intro
              exact assump_78
              exact assump_78
            case inr assump_94 =>
              cases assump_94
              case inl assump_99 =>
                apply Or.inr
                apply And.intro
                exact assump_78
                exact assump_78
              case inr assump_100 =>
                apply False.elim assump_100
        case inr assump_88 =>
          cases assump_86
          case intro assump_109 assump_110 =>
            cases assump_109
            case inl assump_111 =>
              apply Or.inr
              apply And.intro
              exact assump_78
              exact assump_78
            case inr assump_112 =>
              cases assump_112
              case inl assump_117 =>
                apply Or.inr
                apply And.intro
                exact assump_78
                exact assump_78
              case inr assump_118 =>
                apply False.elim assump_118


variable (p2 p1 p7 p3 p6 p4 : Prop)
theorem file2_92513 : (((((p3 ∧ p1) → (p1 → p1)) → False) → False) ∨ ((((p2 ∧ p7) → False) ∧ ((p6 ∧ p3) ∧ (True → False))) → (((True → False) ∨ (p2 ∧ p2)) ∨ ((p1 → False) → (p4 ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((p3 ∧ p1) → (p1 → p1)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p5 p7 p0 p2 p4 : Prop)
theorem file2_93006 : ((((((p5 → p7) ∧ (p0 ∨ p2)) ∧ ((False → False) → False)) → (((p4 ∨ p3) ∨ (False ∨ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_114 : ((((p5 → p7) ∧ (p0 ∨ p2)) ∧ ((False → False) → False)) → (((p4 ∨ p3) ∨ (False ∨ p5)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_16
            case inl assump_19 =>
              have assump_115 : (False → False) := by
                intro assump_26
                apply False.elim assump_26
              let assump_25 := assump_14 assump_115
              apply False.elim assump_25
            case inr assump_20 =>
              have assump_116 : (False → False) := by
                intro assump_37
                apply False.elim assump_37
              let assump_36 := assump_14 assump_116
              apply False.elim assump_36
      case inr assump_10 =>
        cases assump_5
        case intro assump_45 assump_46 =>
          cases assump_45
          case intro assump_47 assump_48 =>
            cases assump_48
            case inl assump_51 =>
              have assump_117 : (False → False) := by
                intro assump_58
                apply False.elim assump_58
              let assump_57 := assump_46 assump_117
              apply False.elim assump_57
            case inr assump_52 =>
              have assump_118 : (False → False) := by
                intro assump_69
                apply False.elim assump_69
              let assump_68 := assump_46 assump_118
              apply False.elim assump_68
    case inr assump_8 =>
      cases assump_8
      case inl assump_75 =>
        apply False.elim assump_75
      case inr assump_76 =>
        cases assump_5
        case intro assump_81 assump_82 =>
          cases assump_81
          case intro assump_83 assump_84 =>
            cases assump_84
            case inl assump_87 =>
              have assump_119 : (False → False) := by
                intro assump_94
                apply False.elim assump_94
              let assump_93 := assump_82 assump_119
              apply False.elim assump_93
            case inr assump_88 =>
              have assump_120 : (False → False) := by
                intro assump_105
                apply False.elim assump_105
              let assump_104 := assump_82 assump_120
              apply False.elim assump_104
  let assump_4 := assump_1 assump_114
  apply False.elim assump_4


variable (p5 p3 p7 p6 p1 p0 : Prop)
theorem file2_95715 : (((((p1 ∨ p6) → False) → ((True → True) ∨ (p1 → False))) ∨ (((True → p1) ∨ (False ∨ p7)) → False)) ∧ ((((p6 → p5) → (True ∨ p3)) → False) → (((p1 ∧ p7) → False) ∧ ((p0 → False) ∨ (p3 ∨ False))))) := by
  apply And.intro
  apply Or.inl
  intro assump_59
  apply Or.inl
  intro assump_62
  apply True.intro
  intro assump_63
  apply And.intro
  intro assump_64
  cases assump_64
  case intro assump_65 assump_66 =>
    have assump_93 : ((p6 → p5) → (True ∨ p3)) := by
      intro assump_74
      apply Or.inl
      apply True.intro
    let assump_73 := assump_63 assump_93
    apply False.elim assump_73
  apply Or.inl
  intro assump_82
  have assump_94 : ((p6 → p5) → (True ∨ p3)) := by
    intro assump_87
    apply Or.inl
    apply True.intro
  let assump_86 := assump_63 assump_94
  apply False.elim assump_86


variable (p6 p1 p3 p5 : Prop)
theorem file2_96581 : ((((((p1 → p1) ∨ (True → p5)) ∨ ((p3 ∨ False) ∧ (True ∨ p1))) ∨ (((p5 ∨ p3) → False) → ((p5 ∨ p6) ∧ (True ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p1 → p1) ∨ (True → p5)) ∨ ((p3 ∨ False) ∧ (True ∨ p1))) ∨ (((p5 ∨ p3) → False) → ((p5 ∨ p6) ∧ (True ∨ True)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p0 : Prop)
theorem file2_97081 : (((((p1 → p1) → False) → ((p0 → False) ∨ (p1 → True))) → False) → False) := by
  intro assump_14
  have assump_35 : (((p1 → p1) → False) → ((p0 → False) ∨ (p1 → True))) := by
    intro assump_18
    apply Or.inl
    intro assump_21
    have assump_36 : (p1 → p1) := by
      intro assump_26
      exact assump_26
    let assump_25 := assump_18 assump_36
    apply False.elim assump_25
  let assump_17 := assump_14 assump_35
  apply False.elim assump_17


variable (p4 p6 p1 p5 p0 p2 : Prop)
theorem file2_97594 : (((((p2 → False) ∨ (p4 → False)) → ((p0 ∧ False) → (p1 → True))) ∧ (((p6 ∨ p5) ∧ (p1 → p6)) ∨ ((p4 → False) → False))) → ((((p4 → p2) ∨ (p0 → p6)) ∧ ((p6 ∨ p1) → False)) → (((p6 ∨ p6) ∨ (p1 → p1)) ∨ ((p5 ∨ p4) ∨ (p6 ∧ p6))))) := by
  intro assump_12
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case inl assump_16 =>
      cases assump_12
      case intro assump_22 assump_23 =>
        cases assump_23
        case inl assump_26 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            cases assump_28
            case inl assump_30 =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_30
            case inr assump_31 =>
              apply Or.inl
              apply Or.inr
              intro assump_40
              exact assump_40
        case inr assump_27 =>
          apply Or.inl
          apply Or.inr
          intro assump_45
          exact assump_45
    case inr assump_17 =>
      cases assump_12
      case intro assump_52 assump_53 =>
        cases assump_53
        case inl assump_56 =>
          cases assump_56
          case intro assump_58 assump_59 =>
            cases assump_58
            case inl assump_60 =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_60
            case inr assump_61 =>
              apply Or.inl
              apply Or.inr
              intro assump_70
              exact assump_70
        case inr assump_57 =>
          apply Or.inl
          apply Or.inr
          intro assump_75
          exact assump_75


variable (p0 p1 p3 p2 : Prop)
theorem file2_99312 : (((((p0 ∧ False) → False) ∨ ((p1 ∨ p3) ∨ (p0 → p1))) → (((p2 ∧ False) → False) → False)) → False) := by
  intro assump_1
  have assump_23 : (((p0 ∧ False) → False) ∨ ((p1 ∨ p3) ∨ (p0 → p1))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_23
  have assump_24 : ((p2 ∧ False) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply False.elim assump_15
  let assump_12 := assump_4 assump_24
  apply False.elim assump_12


variable (p6 p3 p0 p4 p7 p5 : Prop)
theorem file2_99955 : ((((((p0 → False) → (True ∨ p4)) ∧ ((p0 ∧ p7) ∨ (False → False))) ∨ (((p0 → False) → False) ∧ ((p5 ∧ p6) ∨ (p3 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p0 → False) → (True ∨ p4)) ∧ ((p0 ∧ p7) ∨ (False → False))) ∨ (((p0 → False) → False) ∧ ((p5 ∧ p6) ∨ (p3 ∧ p0)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    apply Or.inl
    apply True.intro
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p7 p0 p3 p4 p6 p2 p5 : Prop)
theorem file2_100550 : (((((p1 ∨ p7) ∧ (p5 → False)) ∨ ((p1 → p5) ∨ (True → p6))) → (((False → p2) ∨ (p4 ∨ False)) ∨ ((True → False) ∧ (p7 → p5)))) ∨ ((((p0 → p3) → (True → p6)) ∨ ((p3 → p4) → False)) ∧ (((p2 → True) ∨ (p5 ∨ p4)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        apply Or.inl
        intro assump_12
        apply False.elim assump_12
      case inr assump_7 =>
        apply Or.inl
        apply Or.inl
        intro assump_19
        apply False.elim assump_19
  case inr assump_3 =>
    cases assump_3
    case inl assump_22 =>
      apply Or.inl
      apply Or.inl
      intro assump_26
      apply False.elim assump_26
    case inr assump_23 =>
      apply Or.inl
      apply Or.inl
      intro assump_31
      apply False.elim assump_31


variable (p4 p6 p5 p2 p0 : Prop)
theorem file2_101515 : ((((((p4 ∨ True) ∧ (p5 ∨ p5)) ∧ ((p5 ∨ p5) → False)) → (((p0 → False) → False) ∨ ((p6 ∨ p2) ∧ (p6 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_71 : ((((p4 ∨ True) ∧ (p5 ∨ p5)) ∧ ((p5 ∨ p5) → False)) → (((p0 → False) → False) ∨ ((p6 ∨ p2) ∧ (p6 ∨ p4)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            apply Or.inl
            intro assump_20
            have assump_72 : (p5 ∨ p5) := by
              apply Or.inl
              exact assump_14
            let assump_24 := assump_7 assump_72
            apply False.elim assump_24
          case inr assump_15 =>
            apply Or.inl
            intro assump_32
            have assump_73 : (p5 ∨ p5) := by
              apply Or.inl
              exact assump_15
            let assump_36 := assump_7 assump_73
            apply False.elim assump_36
        case inr assump_11 =>
          cases assump_9
          case inl assump_42 =>
            apply Or.inl
            intro assump_48
            have assump_74 : (p5 ∨ p5) := by
              apply Or.inl
              exact assump_42
            let assump_52 := assump_7 assump_74
            apply False.elim assump_52
          case inr assump_43 =>
            apply Or.inl
            intro assump_60
            have assump_75 : (p5 ∨ p5) := by
              apply Or.inl
              exact assump_43
            let assump_64 := assump_7 assump_75
            apply False.elim assump_64
  let assump_4 := assump_1 assump_71
  apply False.elim assump_4


variable (p3 p1 p5 p7 p4 p2 p6 p0 : Prop)
theorem file2_103286 : (((((False → p1) ∨ (p4 ∧ p1)) ∨ ((p3 → p6) → False)) ∨ (((True → p0) → (p1 → False)) → ((p7 → False) ∧ (True ∨ p1)))) ∨ ((((True → False) ∧ (True ∨ p2)) ∨ ((p2 → p5) → False)) → (((p0 → p3) ∨ (True ∨ p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p3 p5 p2 p1 p7 : Prop)
theorem file2_103670 : (((((p5 → False) ∧ (p7 → False)) ∧ ((True → False) ∨ (p2 → p2))) → (((p3 ∨ True) ∨ (p5 ∧ True)) ∧ ((True ∨ True) ∨ (p3 ∨ p1)))) ∨ ((((p1 → p1) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_11 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
  cases assump_1
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_17
      case inl assump_24 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_25 =>
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p4 p0 p6 p1 p5 p3 : Prop)
theorem file2_104597 : ((((((p1 ∨ p4) ∨ (p0 → True)) ∧ ((p3 → p3) ∨ (p5 → False))) ∧ (((p6 → False) → (p6 → False)) → ((True ∨ p1) ∨ (p0 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p1 ∨ p4) ∨ (p0 → True)) ∧ ((p3 → p3) ∨ (p5 → False))) ∧ (((p6 → False) → (p6 → False)) → ((True ∨ p1) ∨ (p0 ∨ p6)))) := by
    apply And.intro
    apply And.intro
    apply Or.inr
    intro assump_5
    apply True.intro
    apply Or.inl
    intro assump_6
    exact assump_6
    intro assump_9
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p1 p2 p5 p4 p0 : Prop)
theorem file2_105258 : ((((((True → False) → (p1 → False)) ∨ ((p5 → p0) ∨ (p5 ∧ p3))) → False) ∧ ((((False ∧ p4) → (False → False)) ∨ ((p0 ∧ p4) → (p4 → p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((False ∧ p4) → (False → False)) ∨ ((p0 ∧ p4) → (p4 → p2))) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p4 p7 p3 p5 p1 : Prop)
theorem file2_105796 : (((((False ∨ True) ∨ (p5 → True)) ∧ ((False ∧ False) ∧ (p5 ∨ p1))) ∧ (((p3 ∧ p7) → (p4 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply False.elim assump_8
        case inr assump_9 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
      case inr assump_7 =>
        cases assump_5
        case intro assump_22 assump_23 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            apply False.elim assump_24


variable (p4 p1 p6 p0 p2 p5 p7 : Prop)
theorem file2_106654 : ((((((p7 ∨ p4) → False) → False) ∨ (((p4 → p0) → (p1 → False)) ∨ ((p7 → p1) → (p0 ∨ False)))) ∧ ((((p2 ∧ p2) ∨ (p5 → False)) ∧ ((p6 ∨ False) ∧ (p0 → False))) ∧ (((p0 ∧ p4) ∧ (p4 → False)) ∧ ((p6 ∨ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              cases assump_11
              case intro assump_20 assump_21 =>
                cases assump_20
                case inl assump_22 =>
                  cases assump_9
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      cases assump_30
                      case intro assump_32 assump_33 =>
                        have assump_224 : (p6 ∨ p6) := by
                          apply Or.inl
                          exact assump_22
                        let assump_42 := assump_29 assump_224
                        apply False.elim assump_42
                case inr assump_23 =>
                  apply False.elim assump_23
          case inr assump_13 =>
            cases assump_11
            case intro assump_50 assump_51 =>
              cases assump_50
              case inl assump_52 =>
                cases assump_9
                case intro assump_58 assump_59 =>
                  cases assump_58
                  case intro assump_60 assump_61 =>
                    cases assump_60
                    case intro assump_62 assump_63 =>
                      have assump_225 : (p6 ∨ p6) := by
                        apply Or.inl
                        exact assump_52
                      let assump_72 := assump_59 assump_225
                      apply False.elim assump_72
              case inr assump_53 =>
                apply False.elim assump_53
    case inr assump_5 =>
      cases assump_5
      case inl assump_78 =>
        cases assump_3
        case intro assump_82 assump_83 =>
          cases assump_82
          case intro assump_84 assump_85 =>
            cases assump_84
            case inl assump_86 =>
              cases assump_86
              case intro assump_88 assump_89 =>
                cases assump_85
                case intro assump_94 assump_95 =>
                  cases assump_94
                  case inl assump_96 =>
                    cases assump_83
                    case intro assump_102 assump_103 =>
                      cases assump_102
                      case intro assump_104 assump_105 =>
                        cases assump_104
                        case intro assump_106 assump_107 =>
                          have assump_226 : (p6 ∨ p6) := by
                            apply Or.inl
                            exact assump_96
                          let assump_116 := assump_103 assump_226
                          apply False.elim assump_116
                  case inr assump_97 =>
                    apply False.elim assump_97
            case inr assump_87 =>
              cases assump_85
              case intro assump_124 assump_125 =>
                cases assump_124
                case inl assump_126 =>
                  cases assump_83
                  case intro assump_132 assump_133 =>
                    cases assump_132
                    case intro assump_134 assump_135 =>
                      cases assump_134
                      case intro assump_136 assump_137 =>
                        have assump_227 : (p6 ∨ p6) := by
                          apply Or.inl
                          exact assump_126
                        let assump_146 := assump_133 assump_227
                        apply False.elim assump_146
                case inr assump_127 =>
                  apply False.elim assump_127
      case inr assump_79 =>
        cases assump_3
        case intro assump_154 assump_155 =>
          cases assump_154
          case intro assump_156 assump_157 =>
            cases assump_156
            case inl assump_158 =>
              cases assump_158
              case intro assump_160 assump_161 =>
                cases assump_157
                case intro assump_166 assump_167 =>
                  cases assump_166
                  case inl assump_168 =>
                    cases assump_155
                    case intro assump_174 assump_175 =>
                      cases assump_174
                      case intro assump_176 assump_177 =>
                        cases assump_176
                        case intro assump_178 assump_179 =>
                          have assump_228 : (p6 ∨ p6) := by
                            apply Or.inl
                            exact assump_168
                          let assump_188 := assump_175 assump_228
                          apply False.elim assump_188
                  case inr assump_169 =>
                    apply False.elim assump_169
            case inr assump_159 =>
              cases assump_157
              case intro assump_196 assump_197 =>
                cases assump_196
                case inl assump_198 =>
                  cases assump_155
                  case intro assump_204 assump_205 =>
                    cases assump_204
                    case intro assump_206 assump_207 =>
                      cases assump_206
                      case intro assump_208 assump_209 =>
                        have assump_229 : (p6 ∨ p6) := by
                          apply Or.inl
                          exact assump_198
                        let assump_218 := assump_205 assump_229
                        apply False.elim assump_218
                case inr assump_199 =>
                  apply False.elim assump_199


variable (p5 p0 p6 p4 p3 p1 : Prop)
theorem file2_112692 : (((((p4 → p4) ∨ (p1 → p0)) → ((True ∧ True) → False)) ∧ (((p5 ∨ p3) ∧ (p4 ∧ p3)) → ((p6 → p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : ((p4 → p4) ∨ (p1 → p0)) := by
      apply Or.inl
      intro assump_10
      exact assump_10
    let assump_9 := assump_2 assump_17
    have assump_18 : (True ∧ True) := by
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_13 := assump_9 assump_18
    apply False.elim assump_13


variable (p5 p4 p3 p2 p1 p7 : Prop)
theorem file2_113273 : (((((p4 ∨ False) ∨ (p1 ∨ p3)) ∨ ((True → False) → (p5 ∧ False))) → False) → ((((p1 → p1) ∨ (p2 ∨ False)) ∧ ((p3 → False) ∨ (False → p1))) → (((p2 → False) ∧ (p2 ∧ p5)) → ((p7 → False) ∧ (p4 ∨ p4))))) := by
  intro assump_9
  intro assump_10
  intro assump_11
  apply And.intro
  intro assump_12
  cases assump_11
  case intro assump_15 assump_16 =>
    cases assump_16
    case intro assump_19 assump_20 =>
      cases assump_10
      case intro assump_25 assump_26 =>
        cases assump_25
        case inl assump_27 =>
          cases assump_26
          case inl assump_31 =>
            have assump_203 : (((p4 ∨ False) ∨ (p1 ∨ p3)) ∨ ((True → False) → (p5 ∧ False))) := by
              apply Or.inr
              intro assump_38
              apply And.intro
              exact assump_20
              have assump_204 : True := by
                apply True.intro
              let assump_43 := assump_38 assump_204
              apply False.elim assump_43
            let assump_37 := assump_9 assump_203
            apply False.elim assump_37
          case inr assump_32 =>
            have assump_205 : (((p4 ∨ False) ∨ (p1 ∨ p3)) ∨ ((True → False) → (p5 ∧ False))) := by
              apply Or.inr
              intro assump_55
              apply And.intro
              exact assump_20
              have assump_206 : True := by
                apply True.intro
              let assump_60 := assump_55 assump_206
              apply False.elim assump_60
            let assump_54 := assump_9 assump_205
            apply False.elim assump_54
        case inr assump_28 =>
          cases assump_28
          case inl assump_67 =>
            cases assump_26
            case inl assump_71 =>
              have assump_207 : (((p4 ∨ False) ∨ (p1 ∨ p3)) ∨ ((True → False) → (p5 ∧ False))) := by
                apply Or.inr
                intro assump_78
                apply And.intro
                exact assump_20
                have assump_208 : True := by
                  apply True.intro
                let assump_83 := assump_78 assump_208
                apply False.elim assump_83
              let assump_77 := assump_9 assump_207
              apply False.elim assump_77
            case inr assump_72 =>
              have assump_209 : (((p4 ∨ False) ∨ (p1 ∨ p3)) ∨ ((True → False) → (p5 ∧ False))) := by
                apply Or.inr
                intro assump_95
                apply And.intro
                exact assump_20
                have assump_210 : True := by
                  apply True.intro
                let assump_100 := assump_95 assump_210
                apply False.elim assump_100
              let assump_94 := assump_9 assump_209
              apply False.elim assump_94
          case inr assump_68 =>
            apply False.elim assump_68
  cases assump_11
  case intro assump_109 assump_110 =>
    cases assump_110
    case intro assump_113 assump_114 =>
      cases assump_10
      case intro assump_119 assump_120 =>
        cases assump_119
        case inl assump_121 =>
          cases assump_120
          case inl assump_125 =>
            have assump_211 : (((p4 ∨ False) ∨ (p1 ∨ p3)) ∨ ((True → False) → (p5 ∧ False))) := by
              apply Or.inr
              intro assump_132
              apply And.intro
              exact assump_114
              have assump_212 : True := by
                apply True.intro
              let assump_137 := assump_132 assump_212
              apply False.elim assump_137
            let assump_131 := assump_9 assump_211
            apply False.elim assump_131
          case inr assump_126 =>
            have assump_213 : (((p4 ∨ False) ∨ (p1 ∨ p3)) ∨ ((True → False) → (p5 ∧ False))) := by
              apply Or.inr
              intro assump_149
              apply And.intro
              exact assump_114
              have assump_214 : True := by
                apply True.intro
              let assump_154 := assump_149 assump_214
              apply False.elim assump_154
            let assump_148 := assump_9 assump_213
            apply False.elim assump_148
        case inr assump_122 =>
          cases assump_122
          case inl assump_161 =>
            cases assump_120
            case inl assump_165 =>
              have assump_215 : (((p4 ∨ False) ∨ (p1 ∨ p3)) ∨ ((True → False) → (p5 ∧ False))) := by
                apply Or.inr
                intro assump_172
                apply And.intro
                exact assump_114
                have assump_216 : True := by
                  apply True.intro
                let assump_177 := assump_172 assump_216
                apply False.elim assump_177
              let assump_171 := assump_9 assump_215
              apply False.elim assump_171
            case inr assump_166 =>
              have assump_217 : (((p4 ∨ False) ∨ (p1 ∨ p3)) ∨ ((True → False) → (p5 ∧ False))) := by
                apply Or.inr
                intro assump_189
                apply And.intro
                exact assump_114
                have assump_218 : True := by
                  apply True.intro
                let assump_194 := assump_189 assump_218
                apply False.elim assump_194
              let assump_188 := assump_9 assump_217
              apply False.elim assump_188
          case inr assump_162 =>
            apply False.elim assump_162


variable (p1 p2 p0 p5 p7 p3 p4 : Prop)
theorem file2_118699 : (((((p1 ∨ True) → False) ∧ ((p1 → False) → False)) → (((p3 → False) ∨ (p7 ∧ p2)) → ((p0 ∨ p1) → (p0 ∨ p1)))) → ((((p7 ∧ p7) → (p5 ∨ p7)) → ((False → p2) ∨ (p7 → False))) ∨ (((p2 → False) → (p5 ∧ p4)) ∧ ((True ∧ p3) → (p0 ∨ True))))) := by
  intro assump_20
  apply Or.inl
  intro assump_23
  apply Or.inl
  intro assump_26
  apply False.elim assump_26


variable (p0 p2 p3 p5 p4 p1 : Prop)
theorem file2_119111 : (((((p3 ∨ p4) ∨ (p5 ∧ False)) ∧ ((p4 → p0) ∧ (True → False))) → False) ∨ ((((p1 → False) ∧ (p4 ∧ p0)) ∧ ((p0 → False) → (p0 → p1))) ∨ (((p3 ∨ False) ∨ (p0 ∨ p2)) ∧ ((p0 → False) → (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          have assump_38 : True := by
            apply True.intro
          let assump_16 := assump_11 assump_38
          apply False.elim assump_16
      case inr assump_7 =>
        cases assump_3
        case intro assump_22 assump_23 =>
          have assump_39 : True := by
            apply True.intro
          let assump_28 := assump_23 assump_39
          apply False.elim assump_28
    case inr assump_5 =>
      cases assump_5
      case intro assump_32 assump_33 =>
        apply False.elim assump_33


variable (p7 p1 p2 p3 p0 p6 p4 p5 : Prop)
theorem file2_120135 : (((((p3 → p3) → False) → ((p1 → False) ∨ (False → False))) → False) → ((((p4 → p2) → (p3 → False)) ∨ ((p7 → False) ∨ (p4 → False))) ∧ (((p6 → p1) ∧ (p5 ∧ p0)) → False))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_61 : (((p3 → p3) → False) → ((p1 → False) ∨ (False → False))) := by
    intro assump_13
    apply Or.inl
    intro assump_16
    have assump_62 : (p3 → p3) := by
      intro assump_21
      exact assump_21
    let assump_20 := assump_13 assump_62
    apply False.elim assump_20
  let assump_12 := assump_1 assump_61
  apply False.elim assump_12
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    cases assump_32
    case intro assump_35 assump_36 =>
      have assump_63 : (((p3 → p3) → False) → ((p1 → False) ∨ (False → False))) := by
        intro assump_44
        apply Or.inl
        intro assump_47
        have assump_64 : (p3 → p3) := by
          intro assump_52
          exact assump_52
        let assump_51 := assump_44 assump_64
        apply False.elim assump_51
      let assump_43 := assump_1 assump_63
      apply False.elim assump_43


variable (p3 p1 p7 p4 : Prop)
theorem file2_121341 : ((((((p1 → False) → False) → ((True → False) ∧ (p4 → p3))) → False) ∧ ((((p7 → True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p7 → True) → False) → False) := by
      intro assump_9
      have assump_21 : (p7 → True) := by
        intro assump_13
        apply True.intro
      let assump_12 := assump_9 assump_21
      apply False.elim assump_12
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p5 p1 p2 p4 p7 : Prop)
theorem file2_121908 : (((((p2 → False) → False) → ((False ∧ p4) → (p5 → p5))) → False) → ((((p5 ∨ p7) → (p1 ∧ p2)) → ((p2 ∨ True) ∨ (p2 ∨ p2))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_20 : (((p2 → False) → False) → ((False ∧ p4) → (p5 → p5))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  let assump_7 := assump_1 assump_20
  apply False.elim assump_7


variable (p7 p0 p1 p6 p5 p2 p3 : Prop)
theorem file2_122435 : (((((p2 → p5) → (False → False)) → ((p2 ∧ True) ∨ (p3 ∨ True))) → False) → ((((p2 ∨ p5) → (p1 ∨ p3)) ∨ ((p6 → False) → False)) ∨ (((p5 ∧ p7) → (p1 ∨ p7)) ∧ ((p2 ∧ p0) → (True → False))))) := by
  intro assump_9
  apply Or.inl
  apply Or.inl
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    have assump_35 : (((p2 → p5) → (False → False)) → ((p2 ∧ True) ∨ (p3 ∨ True))) := by
      intro assump_19
      apply Or.inl
      apply And.intro
      exact assump_13
      apply True.intro
    let assump_18 := assump_9 assump_35
    apply False.elim assump_18
  case inr assump_14 =>
    have assump_36 : (((p2 → p5) → (False → False)) → ((p2 ∧ True) ∨ (p3 ∨ True))) := by
      intro assump_29
      apply Or.inr
      apply Or.inr
      apply True.intro
    let assump_28 := assump_9 assump_36
    apply False.elim assump_28


variable (p6 p3 p7 p4 p2 p5 : Prop)
theorem file2_123331 : (((((False → False) → False) ∧ ((p3 → p3) ∨ (p6 → p5))) → (((p6 ∧ True) → False) ∧ ((p2 → False) ∨ (p4 ∧ p7)))) ∨ ((((p2 → False) ∧ (p5 ∧ p6)) → ((p2 → p4) → False)) ∨ (((False → False) → False) → False))) := by
  apply Or.inl
  intro assump_9
  apply And.intro
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_9
    case intro assump_17 assump_18 =>
      cases assump_18
      case inl assump_21 =>
        have assump_78 : (False → False) := by
          intro assump_27
          apply False.elim assump_27
        let assump_26 := assump_17 assump_78
        apply False.elim assump_26
      case inr assump_22 =>
        have assump_79 : (False → False) := by
          intro assump_38
          apply False.elim assump_38
        let assump_37 := assump_17 assump_79
        apply False.elim assump_37
  cases assump_9
  case intro assump_44 assump_45 =>
    cases assump_45
    case inl assump_48 =>
      apply Or.inl
      intro assump_52
      have assump_80 : (False → False) := by
        intro assump_58
        apply False.elim assump_58
      let assump_57 := assump_44 assump_80
      apply False.elim assump_57
    case inr assump_49 =>
      apply Or.inl
      intro assump_66
      have assump_81 : (False → False) := by
        intro assump_72
        apply False.elim assump_72
      let assump_71 := assump_44 assump_81
      apply False.elim assump_71


variable (p3 p2 p6 p1 p5 p4 p7 p0 : Prop)
theorem file2_124813 : (((((p5 ∨ True) ∨ (p7 → p1)) ∨ ((p7 ∨ p6) → (p3 ∨ p3))) → (((False → False) → False) → ((p4 ∧ p0) ∧ (p0 ∨ p7)))) ∧ ((((p3 → True) → False) → ((p5 ∧ p5) ∨ (p4 → False))) ∨ (((p1 ∨ p3) → (p1 → p7)) → ((p2 → p3) → (p4 ∧ p3))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_156 : (False → False) := by
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_2 assump_156
        apply False.elim assump_14
      case inr assump_10 =>
        have assump_157 : (False → False) := by
          intro assump_24
          apply False.elim assump_24
        let assump_23 := assump_2 assump_157
        apply False.elim assump_23
    case inr assump_8 =>
      have assump_158 : (False → False) := by
        intro assump_34
        apply False.elim assump_34
      let assump_33 := assump_2 assump_158
      apply False.elim assump_33
  case inr assump_6 =>
    have assump_159 : (False → False) := by
      intro assump_44
      apply False.elim assump_44
    let assump_43 := assump_2 assump_159
    apply False.elim assump_43
  cases assump_1
  case inl assump_52 =>
    cases assump_52
    case inl assump_54 =>
      cases assump_54
      case inl assump_56 =>
        have assump_160 : (False → False) := by
          intro assump_62
          apply False.elim assump_62
        let assump_61 := assump_2 assump_160
        apply False.elim assump_61
      case inr assump_57 =>
        have assump_161 : (False → False) := by
          intro assump_71
          apply False.elim assump_71
        let assump_70 := assump_2 assump_161
        apply False.elim assump_70
    case inr assump_55 =>
      have assump_162 : (False → False) := by
        intro assump_81
        apply False.elim assump_81
      let assump_80 := assump_2 assump_162
      apply False.elim assump_80
  case inr assump_53 =>
    have assump_163 : (False → False) := by
      intro assump_91
      apply False.elim assump_91
    let assump_90 := assump_2 assump_163
    apply False.elim assump_90
  cases assump_1
  case inl assump_99 =>
    cases assump_99
    case inl assump_101 =>
      cases assump_101
      case inl assump_103 =>
        have assump_164 : (False → False) := by
          intro assump_109
          apply False.elim assump_109
        let assump_108 := assump_2 assump_164
        apply False.elim assump_108
      case inr assump_104 =>
        have assump_165 : (False → False) := by
          intro assump_118
          apply False.elim assump_118
        let assump_117 := assump_2 assump_165
        apply False.elim assump_117
    case inr assump_102 =>
      have assump_166 : (False → False) := by
        intro assump_128
        apply False.elim assump_128
      let assump_127 := assump_2 assump_166
      apply False.elim assump_127
  case inr assump_100 =>
    have assump_167 : (False → False) := by
      intro assump_138
      apply False.elim assump_138
    let assump_137 := assump_2 assump_167
    apply False.elim assump_137
  apply Or.inl
  intro assump_144
  apply Or.inr
  intro assump_147
  have assump_168 : (p3 → True) := by
    intro assump_152
    apply True.intro
  let assump_151 := assump_144 assump_168
  apply False.elim assump_151


variable (p1 p5 p0 p7 p6 p3 p4 : Prop)
theorem file2_128277 : ((((((p6 ∨ True) ∧ (False ∧ p0)) → False) ∧ (((p5 → p7) → False) ∧ ((True → False) → (p3 → False)))) ∧ ((((p5 ∧ p7) ∨ (p4 ∧ p5)) → False) ∧ (((False → p1) ∨ (p5 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          have assump_27 : ((False → p1) ∨ (p5 ∨ True)) := by
            apply Or.inl
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_15 assump_27
          apply False.elim assump_20


variable (p1 p7 p3 p2 p0 p6 p4 : Prop)
theorem file2_129021 : ((((((p4 → False) ∧ (False ∧ p2)) → False) → False) ∧ ((((p0 ∧ True) ∨ (p0 ∧ p6)) → False) ∨ (((p3 ∧ p4) → False) ∧ ((p7 ∧ False) ∧ (p4 ∨ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_36 : (((p4 → False) ∧ (False ∧ p2)) → False) := by
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
      let assump_11 := assump_2 assump_36
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            apply False.elim assump_31


