variable (p0 p2 p4 p7 : Prop)
theorem file54_38 : ((((((False → p2) → False) ∨ ((p7 ∨ p7) ∧ (p0 ∧ p4))) → (((False → False) ∧ (p4 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_61 : ((((False → p2) → False) ∨ ((p7 ∨ p7) ∧ (p0 ∧ p4))) → (((False → False) ∧ (p4 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case inl assump_13 =>
        have assump_62 : (False → p2) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_13 assump_62
        apply False.elim assump_17
      case inr assump_14 =>
        cases assump_14
        case intro assump_24 assump_25 =>
          cases assump_24
          case inl assump_26 =>
            cases assump_25
            case intro assump_30 assump_31 =>
              have assump_63 : p4 := by
                exact assump_31
              let assump_39 := assump_8 assump_63
              apply False.elim assump_39
          case inr assump_27 =>
            cases assump_25
            case intro assump_45 assump_46 =>
              have assump_64 : p4 := by
                exact assump_46
              let assump_54 := assump_8 assump_64
              apply False.elim assump_54
  let assump_4 := assump_1 assump_61
  apply False.elim assump_4


variable (p0 p6 : Prop)
theorem file54_1402 : (((((p6 ∧ p0) ∧ (p6 → False)) → False) → False) → False) := by
  intro assump_1
  have assump_23 : (((p6 ∧ p0) ∧ (p6 → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_24 : p6 := by
          exact assump_8
        let assump_16 := assump_7 assump_24
        apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p1 p5 p0 p6 p2 : Prop)
theorem file54_1940 : (((((p3 ∨ p5) → False) ∧ ((False → False) ∨ (False → False))) ∨ (((p1 → False) ∨ (p1 → p5)) ∧ ((p2 ∨ p5) → False))) → ((((True → False) ∨ (False ∧ p0)) → ((p6 → p0) ∨ (True ∨ False))) ∧ (((True ∨ p5) ∨ (p0 → False)) ∨ ((False → False) ∨ (p3 ∧ p3))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_10
        case inl assump_13 =>
          apply Or.inl
          intro assump_17
          have assump_99 : True := by
            apply True.intro
          let assump_23 := assump_3 assump_99
          apply False.elim assump_23
        case inr assump_14 =>
          apply Or.inl
          intro assump_29
          have assump_100 : True := by
            apply True.intro
          let assump_35 := assump_3 assump_100
          apply False.elim assump_35
    case inr assump_8 =>
      cases assump_8
      case intro assump_39 assump_40 =>
        cases assump_39
        case inl assump_41 =>
          apply Or.inl
          intro assump_47
          have assump_101 : True := by
            apply True.intro
          let assump_53 := assump_3 assump_101
          apply False.elim assump_53
        case inr assump_42 =>
          apply Or.inl
          intro assump_61
          have assump_102 : True := by
            apply True.intro
          let assump_67 := assump_3 assump_102
          apply False.elim assump_67
  case inr assump_4 =>
    cases assump_4
    case intro assump_71 assump_72 =>
      apply False.elim assump_71
  cases assump_1
  case inl assump_75 =>
    cases assump_75
    case intro assump_77 assump_78 =>
      cases assump_78
      case inl assump_81 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_82 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
  case inr assump_76 =>
    cases assump_76
    case intro assump_87 assump_88 =>
      cases assump_87
      case inl assump_89 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_90 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p7 p6 p5 p1 p0 p3 p4 p2 : Prop)
theorem file54_4317 : (((((p2 ∧ p0) → (p2 ∨ p0)) ∨ ((p6 ∧ True) ∧ (p4 → False))) ∨ (((p1 → p3) ∨ (True ∧ p5)) → False)) ∨ ((((p3 ∨ p4) → (p2 → p1)) ∨ ((p5 ∧ p1) → (p6 → False))) → (((p7 → False) → (False ∧ p3)) → ((p6 ∧ p3) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    apply Or.inl
    exact assump_12


variable (p0 p2 p5 p7 p4 p3 : Prop)
theorem file54_4751 : (((((False → p4) → False) ∨ ((True ∨ p0) → (p5 → False))) ∧ (((p0 ∨ p2) ∨ (p3 ∧ p7)) → False)) → ((((p3 ∧ False) → False) ∧ ((p2 → False) → False)) → (((p7 ∨ True) ∧ (False → False)) → ((True ∧ True) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case intro assump_11 assump_12 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_2
        case intro assump_19 assump_20 =>
          cases assump_1
          case intro assump_25 assump_26 =>
            cases assump_25
            case inl assump_27 =>
              have assump_105 : (False → p4) := by
                intro assump_35
                apply False.elim assump_35
              let assump_34 := assump_27 assump_105
              apply False.elim assump_34
            case inr assump_28 =>
              have assump_106 : (p2 → False) := by
                intro assump_49
                have assump_107 : ((p0 ∨ p2) ∨ (p3 ∧ p7)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_49
                let assump_53 := assump_26 assump_107
                apply False.elim assump_53
              let assump_48 := assump_20 assump_106
              apply False.elim assump_48
      case inr assump_14 =>
        cases assump_2
        case intro assump_64 assump_65 =>
          cases assump_1
          case intro assump_70 assump_71 =>
            cases assump_70
            case inl assump_72 =>
              have assump_108 : (False → p4) := by
                intro assump_80
                apply False.elim assump_80
              let assump_79 := assump_72 assump_108
              apply False.elim assump_79
            case inr assump_73 =>
              have assump_109 : (p2 → False) := by
                intro assump_94
                have assump_110 : ((p0 ∨ p2) ∨ (p3 ∧ p7)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_94
                let assump_98 := assump_71 assump_110
                apply False.elim assump_98
              let assump_93 := assump_65 assump_109
              apply False.elim assump_93


variable (p0 p3 p5 p1 p6 : Prop)
theorem file54_7044 : (((((p5 ∧ p5) → (p1 ∨ p6)) → ((p5 ∨ p3) → False)) ∨ (((p6 → p1) → False) → ((False → False) → False))) → ((((p1 ∧ False) ∨ (p3 ∧ True)) ∨ ((p3 ∧ p0) ∨ (p3 → False))) → (((p3 → False) ∨ (p6 ∨ p5)) → ((p1 → False) → (False → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply True.intro


variable (p0 p4 p5 p7 p6 : Prop)
theorem file54_7444 : ((((((p5 ∨ p6) ∧ (p7 ∧ False)) ∨ ((True → p0) → (False → p7))) ∨ (((p7 ∨ p0) ∨ (p5 ∧ p4)) ∧ ((p7 ∧ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p5 ∨ p6) ∧ (p7 ∧ False)) ∨ ((True → p0) → (False → p7))) ∨ (((p7 ∨ p0) ∨ (p5 ∧ p4)) ∧ ((p7 ∧ p7) → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p1 p6 p5 p4 p0 p7 : Prop)
theorem file54_7966 : ((((((p5 ∧ p6) → False) → ((False → p1) ∨ (p0 → False))) ∨ (((p2 → p7) → False) → False)) → ((((True ∧ True) ∨ (p4 → False)) → False) ∧ (((p4 ∨ False) → (True → p1)) ∨ ((False ∧ p4) → (p1 ∧ False))))) → False) := by
  intro assump_1
  have assump_16 : ((((p5 ∧ p6) → False) → ((False → p1) ∨ (p0 → False))) ∨ (((p2 → p7) → False) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  let assump_11 := And.left assump_4
  have assump_17 : ((True ∧ True) ∨ (p4 → False)) := by
    apply Or.inl
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_12 := assump_11 assump_17
  apply False.elim assump_12


variable (p4 p3 p5 p7 p1 p0 p6 : Prop)
theorem file54_8754 : ((((((p3 ∨ True) ∨ (p4 → False)) ∨ ((p3 → p7) ∨ (p5 → p6))) → False) ∨ ((((p1 ∧ False) ∨ (p0 → False)) → ((p4 ∨ False) → (True ∨ p3))) ∧ (((p0 ∧ p4) ∨ (p6 ∨ p7)) ∧ ((True → False) ∧ (True → p1))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_66 : (((p3 ∨ True) ∨ (p4 → False)) ∨ ((p3 → p7) ∨ (p5 → p6))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_6 := assump_2 assump_66
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_15
            case intro assump_24 assump_25 =>
              have assump_67 : True := by
                apply True.intro
              let assump_32 := assump_24 assump_67
              apply False.elim assump_32
        case inr assump_17 =>
          cases assump_17
          case inl assump_36 =>
            cases assump_15
            case intro assump_40 assump_41 =>
              have assump_68 : True := by
                apply True.intro
              let assump_48 := assump_40 assump_68
              apply False.elim assump_48
          case inr assump_37 =>
            cases assump_15
            case intro assump_54 assump_55 =>
              have assump_69 : True := by
                apply True.intro
              let assump_62 := assump_54 assump_69
              apply False.elim assump_62


variable (p4 p3 p1 p0 p7 p5 p6 : Prop)
theorem file54_10429 : (((((p6 ∨ True) ∨ (True ∨ p3)) ∨ ((p7 ∨ p3) ∧ (p0 → False))) ∨ (((p0 → False) → (False → p4)) → ((p1 ∧ p4) → (p5 ∨ p4)))) ∨ ((((p3 ∧ True) → (True → False)) → False) ∨ (((p1 ∧ True) → False) ∨ ((p1 → p0) → (p7 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p4 p6 p2 p7 p0 p1 p5 p3 : Prop)
theorem file54_10815 : (((((p6 → p3) ∧ (p5 ∨ p6)) ∧ ((True → p4) → False)) → (((p4 → p3) → (p7 → False)) → ((False ∧ p3) → False))) ∨ ((((False → False) ∧ (p7 → p2)) ∧ ((p4 → p6) → (p1 ∧ p0))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4


variable (p2 p4 p5 p3 : Prop)
theorem file54_11202 : (((((False → p4) ∧ (True → False)) ∧ ((False ∧ p4) → False)) ∧ (((True ∨ p4) ∨ (p2 ∧ p5)) ∧ ((p3 ∨ True) ∧ (True → False)))) → False) := by
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    cases assump_29
    case intro assump_31 assump_32 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        cases assump_30
        case intro assump_41 assump_42 =>
          cases assump_41
          case inl assump_43 =>
            cases assump_43
            case inl assump_45 =>
              cases assump_42
              case intro assump_49 assump_50 =>
                cases assump_49
                case inl assump_51 =>
                  have assump_117 : True := by
                    apply True.intro
                  let assump_57 := assump_50 assump_117
                  apply False.elim assump_57
                case inr assump_52 =>
                  have assump_118 : True := by
                    apply True.intro
                  let assump_65 := assump_50 assump_118
                  apply False.elim assump_65
            case inr assump_46 =>
              cases assump_42
              case intro assump_71 assump_72 =>
                cases assump_71
                case inl assump_73 =>
                  have assump_119 : True := by
                    apply True.intro
                  let assump_79 := assump_72 assump_119
                  apply False.elim assump_79
                case inr assump_74 =>
                  have assump_120 : True := by
                    apply True.intro
                  let assump_87 := assump_72 assump_120
                  apply False.elim assump_87
          case inr assump_44 =>
            cases assump_44
            case intro assump_91 assump_92 =>
              cases assump_42
              case intro assump_97 assump_98 =>
                cases assump_97
                case inl assump_99 =>
                  have assump_121 : True := by
                    apply True.intro
                  let assump_105 := assump_98 assump_121
                  apply False.elim assump_105
                case inr assump_100 =>
                  have assump_122 : True := by
                    apply True.intro
                  let assump_113 := assump_98 assump_122
                  apply False.elim assump_113


variable (p1 p0 p7 p2 p4 p3 p6 p5 : Prop)
theorem file54_13599 : (((((p3 ∧ p2) ∨ (p1 → p3)) → ((p7 → False) ∧ (False → False))) ∧ (((p7 ∨ p6) → False) ∧ ((p2 ∨ False) → (p4 ∨ False)))) → ((((p7 ∨ p1) ∧ (p5 ∨ False)) ∧ ((p2 → False) ∨ (True ∨ p6))) ∨ (((p1 → p0) → (p7 → False)) ∨ ((p3 ∧ p0) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inr
      apply Or.inl
      intro assump_12
      intro assump_13
      have assump_25 : (p7 ∨ p6) := by
        apply Or.inl
        exact assump_13
      let assump_21 := assump_6 assump_25
      apply False.elim assump_21


variable (p7 p5 p0 p4 p6 p2 p1 p3 : Prop)
theorem file54_14273 : (((((p1 → p3) → False) ∨ ((p1 ∧ False) ∧ (p3 → False))) ∧ (((p4 → False) ∧ (p3 → False)) ∨ ((p0 ∧ True) ∨ (p0 ∧ p2)))) → ((((p2 ∨ p2) ∨ (p5 → p2)) ∧ ((p5 ∨ p7) → False)) → (((p3 ∧ p6) → (p3 ∨ False)) ∨ ((p6 ∧ p2) ∧ (p6 → p5))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_1
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_14
            case inl assump_19 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                apply Or.inl
                intro assump_27
                cases assump_27
                case intro assump_28 assump_29 =>
                  apply Or.inl
                  exact assump_28
            case inr assump_20 =>
              cases assump_20
              case inl assump_34 =>
                cases assump_34
                case intro assump_36 assump_37 =>
                  apply Or.inl
                  intro assump_42
                  cases assump_42
                  case intro assump_43 assump_44 =>
                    apply Or.inl
                    exact assump_43
              case inr assump_35 =>
                cases assump_35
                case intro assump_49 assump_50 =>
                  apply Or.inl
                  intro assump_55
                  cases assump_55
                  case intro assump_56 assump_57 =>
                    apply Or.inl
                    exact assump_56
          case inr assump_16 =>
            cases assump_16
            case intro assump_62 assump_63 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                apply False.elim assump_65
      case inr assump_8 =>
        cases assump_1
        case intro assump_74 assump_75 =>
          cases assump_74
          case inl assump_76 =>
            cases assump_75
            case inl assump_80 =>
              cases assump_80
              case intro assump_82 assump_83 =>
                apply Or.inl
                intro assump_88
                cases assump_88
                case intro assump_89 assump_90 =>
                  apply Or.inl
                  exact assump_89
            case inr assump_81 =>
              cases assump_81
              case inl assump_95 =>
                cases assump_95
                case intro assump_97 assump_98 =>
                  apply Or.inl
                  intro assump_103
                  cases assump_103
                  case intro assump_104 assump_105 =>
                    apply Or.inl
                    exact assump_104
              case inr assump_96 =>
                cases assump_96
                case intro assump_110 assump_111 =>
                  apply Or.inl
                  intro assump_116
                  cases assump_116
                  case intro assump_117 assump_118 =>
                    apply Or.inl
                    exact assump_117
          case inr assump_77 =>
            cases assump_77
            case intro assump_123 assump_124 =>
              cases assump_123
              case intro assump_125 assump_126 =>
                apply False.elim assump_126
    case inr assump_6 =>
      cases assump_1
      case intro assump_135 assump_136 =>
        cases assump_135
        case inl assump_137 =>
          cases assump_136
          case inl assump_141 =>
            cases assump_141
            case intro assump_143 assump_144 =>
              apply Or.inl
              intro assump_149
              cases assump_149
              case intro assump_150 assump_151 =>
                apply Or.inl
                exact assump_150
          case inr assump_142 =>
            cases assump_142
            case inl assump_156 =>
              cases assump_156
              case intro assump_158 assump_159 =>
                apply Or.inl
                intro assump_164
                cases assump_164
                case intro assump_165 assump_166 =>
                  apply Or.inl
                  exact assump_165
            case inr assump_157 =>
              cases assump_157
              case intro assump_171 assump_172 =>
                apply Or.inl
                intro assump_177
                cases assump_177
                case intro assump_178 assump_179 =>
                  apply Or.inl
                  exact assump_178
        case inr assump_138 =>
          cases assump_138
          case intro assump_184 assump_185 =>
            cases assump_184
            case intro assump_186 assump_187 =>
              apply False.elim assump_187


variable (p2 p4 p6 p7 p1 p0 p3 : Prop)
theorem file54_19094 : (((((p3 → True) ∨ (p6 → p6)) ∨ ((p6 ∧ p0) ∧ (p2 ∧ p4))) → (((p3 → False) → (p0 → p6)) ∧ ((False ∨ False) ∨ (p3 ∧ p4)))) → ((((True → False) → False) ∨ ((p4 → p4) ∨ (True ∨ p1))) ∨ (((p0 ∧ p7) → (p3 ∨ p1)) ∨ ((False → p2) → (p6 ∨ p2))))) := by
  intro assump_7
  apply Or.inl
  apply Or.inl
  intro assump_10
  have assump_17 : True := by
    apply True.intro
  let assump_13 := assump_10 assump_17
  apply False.elim assump_13


variable (p2 p3 p6 p1 p4 : Prop)
theorem file54_19578 : ((((((True ∨ p1) → False) → ((p1 ∧ p6) ∨ (p3 → p1))) → (((p2 → True) → False) → ((p1 ∨ True) ∨ (p4 → True)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((True ∨ p1) → False) → ((p1 ∧ p6) ∨ (p3 → p1))) → (((p2 → True) → False) → ((p1 ∨ True) ∨ (p4 → True)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p3 p5 p4 p1 p7 p2 p6 : Prop)
theorem file54_20083 : (((((p3 ∧ p4) ∨ (p5 ∧ p2)) → ((p6 → True) ∨ (p1 ∨ p4))) ∨ (((p1 → False) ∧ (False → False)) → False)) ∨ ((((p1 → False) ∨ (p4 → p7)) ∧ ((p6 → p4) → (True → False))) → (((False ∨ p1) ∧ (p2 → p1)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_10
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_11 assump_12 =>
      apply Or.inl
      intro assump_17
      apply True.intro


variable (p7 p4 p6 p0 p5 p1 p2 : Prop)
theorem file54_20708 : (((((p7 → False) → False) ∧ ((p2 ∨ p0) → False)) → (((p2 ∧ p6) → False) ∨ ((p1 ∧ p7) ∨ (True ∧ p4)))) ∨ ((((p6 ∧ False) → False) ∨ ((p5 → False) → (p4 ∨ False))) ∨ (((p5 → False) ∧ (True → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_21 : (p2 ∨ p0) := by
        apply Or.inl
        exact assump_9
      let assump_17 := assump_3 assump_21
      apply False.elim assump_17


variable (p6 p4 p7 : Prop)
theorem file54_21306 : (((((p7 ∨ p6) ∨ (p6 → False)) → False) → False) ∨ ((((p4 ∨ p4) → (p7 ∨ p7)) → ((p6 → False) ∨ (False → False))) → False)) := by
  apply Or.inl
  intro assump_10
  have assump_25 : ((p7 ∨ p6) ∨ (p6 → False)) := by
    apply Or.inr
    intro assump_14
    have assump_26 : ((p7 ∨ p6) ∨ (p6 → False)) := by
      apply Or.inl
      apply Or.inr
      exact assump_14
    let assump_18 := assump_10 assump_26
    apply False.elim assump_18
  let assump_13 := assump_10 assump_25
  apply False.elim assump_13


variable (p3 p7 p4 p5 p6 : Prop)
theorem file54_21867 : (((((p3 → False) → (p7 ∨ p3)) ∧ ((p4 → p5) ∧ (True → False))) ∧ (((False → p6) → (True ∨ p5)) → False)) → ((((p3 ∧ True) ∨ (True ∧ p3)) ∧ ((p5 → False) ∨ (True ∧ True))) → False)) := by
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
          cases assump_1
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_20
              case intro assump_23 assump_24 =>
                have assump_123 : ((False → p6) → (True ∨ p5)) := by
                  intro assump_32
                  apply Or.inl
                  apply True.intro
                let assump_31 := assump_18 assump_123
                apply False.elim assump_31
        case inr assump_14 =>
          cases assump_14
          case intro assump_38 assump_39 =>
            cases assump_1
            case intro assump_44 assump_45 =>
              cases assump_44
              case intro assump_46 assump_47 =>
                cases assump_47
                case intro assump_50 assump_51 =>
                  have assump_124 : ((False → p6) → (True ∨ p5)) := by
                    intro assump_59
                    apply Or.inl
                    apply True.intro
                  let assump_58 := assump_45 assump_124
                  apply False.elim assump_58
    case inr assump_6 =>
      cases assump_6
      case intro assump_65 assump_66 =>
        cases assump_4
        case inl assump_71 =>
          cases assump_1
          case intro assump_75 assump_76 =>
            cases assump_75
            case intro assump_77 assump_78 =>
              cases assump_78
              case intro assump_81 assump_82 =>
                have assump_125 : ((False → p6) → (True ∨ p5)) := by
                  intro assump_90
                  apply Or.inl
                  apply True.intro
                let assump_89 := assump_76 assump_125
                apply False.elim assump_89
        case inr assump_72 =>
          cases assump_72
          case intro assump_96 assump_97 =>
            cases assump_1
            case intro assump_102 assump_103 =>
              cases assump_102
              case intro assump_104 assump_105 =>
                cases assump_105
                case intro assump_108 assump_109 =>
                  have assump_126 : ((False → p6) → (True ∨ p5)) := by
                    intro assump_117
                    apply Or.inl
                    apply True.intro
                  let assump_116 := assump_103 assump_126
                  apply False.elim assump_116


variable (p6 p1 p0 p7 p5 p2 p3 : Prop)
theorem file54_24704 : (((((p6 ∧ p2) ∧ (p1 → False)) ∨ ((p3 ∨ p2) → (p5 → p6))) → (((p6 ∨ False) → False) → False)) → ((((p1 ∧ False) ∧ (p1 ∧ p7)) ∧ ((False → False) ∨ (p6 → False))) ∨ (((p0 → False) ∨ (True ∨ True)) → ((False → False) ∨ (False → False))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  case inr assump_6 =>
    cases assump_6
    case inl assump_12 =>
      apply Or.inl
      intro assump_16
      apply False.elim assump_16
    case inr assump_13 =>
      apply Or.inl
      intro assump_21
      apply False.elim assump_21


variable (p1 p3 p4 p7 p6 p5 : Prop)
theorem file54_25402 : (((((p3 → p4) → False) ∨ ((p1 → p5) ∧ (p6 ∧ p4))) → False) → ((((p5 → p5) → False) → False) ∨ (((p7 → False) → False) ∧ ((True ∨ p3) → (p5 ∨ p4))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (p5 → p5) := by
    intro assump_8
    exact assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p2 : Prop)
theorem file54_25789 : ((((((p2 ∧ False) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p2 ∧ False) → False) → False) → False) := by
    intro assump_5
    have assump_23 : ((p2 ∧ False) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p3 p4 p7 p6 p5 p1 p2 : Prop)
theorem file54_26329 : (((((p3 ∧ False) → (p1 → p4)) → False) ∧ (((p5 → p2) ∧ (p1 → False)) ∨ ((p1 → False) ∨ (p6 ∨ p4)))) → ((((p7 → p0) → (p6 ∨ p0)) → False) ∧ (((True ∨ False) → (p0 ∨ p3)) → ((p4 → False) → False)))) := by
  intro assump_9
  apply And.intro
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    cases assump_14
    case inl assump_17 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        have assump_185 : ((p3 ∧ False) → (p1 → p4)) := by
          intro assump_28
          intro assump_29
          cases assump_28
          case intro assump_32 assump_33 =>
            apply False.elim assump_33
        let assump_27 := assump_13 assump_185
        apply False.elim assump_27
    case inr assump_18 =>
      cases assump_18
      case inl assump_41 =>
        have assump_186 : ((p3 ∧ False) → (p1 → p4)) := by
          intro assump_47
          intro assump_48
          cases assump_47
          case intro assump_51 assump_52 =>
            apply False.elim assump_52
        let assump_46 := assump_13 assump_186
        apply False.elim assump_46
      case inr assump_42 =>
        cases assump_42
        case inl assump_60 =>
          have assump_187 : ((p3 ∧ False) → (p1 → p4)) := by
            intro assump_66
            intro assump_67
            cases assump_66
            case intro assump_70 assump_71 =>
              apply False.elim assump_71
          let assump_65 := assump_13 assump_187
          apply False.elim assump_65
        case inr assump_61 =>
          have assump_188 : ((p3 ∧ False) → (p1 → p4)) := by
            intro assump_83
            intro assump_84
            cases assump_83
            case intro assump_87 assump_88 =>
              apply False.elim assump_88
          let assump_82 := assump_13 assump_188
          apply False.elim assump_82
  intro assump_96
  intro assump_97
  cases assump_9
  case intro assump_102 assump_103 =>
    cases assump_103
    case inl assump_106 =>
      cases assump_106
      case intro assump_108 assump_109 =>
        have assump_189 : ((p3 ∧ False) → (p1 → p4)) := by
          intro assump_117
          intro assump_118
          cases assump_117
          case intro assump_121 assump_122 =>
            apply False.elim assump_122
        let assump_116 := assump_102 assump_189
        apply False.elim assump_116
    case inr assump_107 =>
      cases assump_107
      case inl assump_130 =>
        have assump_190 : ((p3 ∧ False) → (p1 → p4)) := by
          intro assump_136
          intro assump_137
          cases assump_136
          case intro assump_140 assump_141 =>
            apply False.elim assump_141
        let assump_135 := assump_102 assump_190
        apply False.elim assump_135
      case inr assump_131 =>
        cases assump_131
        case inl assump_149 =>
          have assump_191 : ((p3 ∧ False) → (p1 → p4)) := by
            intro assump_155
            intro assump_156
            cases assump_155
            case intro assump_159 assump_160 =>
              apply False.elim assump_160
          let assump_154 := assump_102 assump_191
          apply False.elim assump_154
        case inr assump_150 =>
          have assump_192 : ((p3 ∧ False) → (p1 → p4)) := by
            intro assump_172
            intro assump_173
            cases assump_172
            case intro assump_176 assump_177 =>
              apply False.elim assump_177
          let assump_171 := assump_102 assump_192
          apply False.elim assump_171


variable (p7 p6 p4 p1 p0 p2 p3 p5 : Prop)
theorem file54_29907 : (((((p0 → False) ∧ (p1 → p5)) → False) ∨ (((True → p1) → (False ∨ p1)) ∧ ((False ∧ False) ∧ (p6 → p0)))) → ((((p2 → False) → (p5 → True)) ∨ ((p7 ∧ p4) → False)) → (((p0 ∧ False) → False) ∨ ((p3 ∨ True) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      apply Or.inl
      intro assump_11
      cases assump_11
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case intro assump_18 assump_19 =>
        cases assump_19
        case intro assump_22 assump_23 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            apply False.elim assump_24
  case inr assump_4 =>
    cases assump_1
    case inl assump_30 =>
      apply Or.inl
      intro assump_34
      cases assump_34
      case intro assump_35 assump_36 =>
        apply False.elim assump_36
    case inr assump_31 =>
      cases assump_31
      case intro assump_41 assump_42 =>
        cases assump_42
        case intro assump_45 assump_46 =>
          cases assump_45
          case intro assump_47 assump_48 =>
            apply False.elim assump_47


variable (p0 p3 p6 p5 : Prop)
theorem file54_31167 : (((((p6 ∧ p3) → (p3 ∨ p0)) ∨ ((p5 ∨ p0) ∧ (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p6 ∧ p3) → (p3 ∨ p0)) ∨ ((p5 ∨ p0) ∧ (p5 → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      exact assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p7 p2 p5 p0 p4 : Prop)
theorem file54_31601 : (((((False ∧ p5) → (p2 ∧ p0)) ∨ ((p7 → False) → False)) ∧ (((p5 → False) → False) ∨ ((p5 ∧ p7) → False))) → ((((p6 → False) → False) ∧ ((p0 → p2) ∧ (p5 ∧ p2))) → (((p6 → p0) → (False → False)) ∧ ((p7 ∧ False) ∨ (p4 ∨ p2))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  apply False.elim assump_4
  cases assump_2
  case intro assump_7 assump_8 =>
    cases assump_8
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        cases assump_1
        case intro assump_21 assump_22 =>
          cases assump_21
          case inl assump_23 =>
            cases assump_22
            case inl assump_27 =>
              apply Or.inr
              apply Or.inr
              exact assump_16
            case inr assump_28 =>
              apply Or.inr
              apply Or.inr
              exact assump_16
          case inr assump_24 =>
            cases assump_22
            case inl assump_35 =>
              apply Or.inr
              apply Or.inr
              exact assump_16
            case inr assump_36 =>
              apply Or.inr
              apply Or.inr
              exact assump_16


variable (p1 p0 p7 p4 p5 p2 p3 : Prop)
theorem file54_32862 : (((((p1 ∧ False) ∧ (False → False)) → ((False → True) → (p1 ∨ p1))) → (((p0 ∨ p4) ∧ (p2 → False)) ∧ ((p4 ∨ True) ∨ (p3 ∨ p7)))) → ((((p7 ∨ p7) ∧ (p3 ∨ p0)) ∨ ((p5 ∧ True) → (True → p7))) → (((p1 ∧ p0) ∧ (p5 → False)) → ((p2 ∧ p2) → (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p2 p1 p0 p7 p5 p3 : Prop)
theorem file54_33293 : ((((((False ∧ p1) ∧ (p3 ∧ p7)) → False) → (((p7 ∨ p3) ∧ (p0 ∧ p3)) ∧ ((p5 → False) → False))) ∧ ((((p7 → p3) → (False → p3)) ∨ ((p3 ∨ False) → (p7 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p7 → p3) → (False → p3)) ∨ ((p3 ∨ False) → (p7 ∧ p2))) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p6 p3 p4 p5 p7 p1 : Prop)
theorem file54_33850 : (((((p5 → p3) → False) → ((p6 ∨ True) → (False → False))) ∧ (((p5 ∨ p1) ∧ (False ∧ p6)) ∧ ((p3 → p4) ∧ (True → p7)))) → False) := by
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
            apply False.elim assump_14
        case inr assump_11 =>
          cases assump_9
          case intro assump_20 assump_21 =>
            apply False.elim assump_20


variable (p3 p0 : Prop)
theorem file54_34512 : (((((p3 → p0) ∧ (False → False)) → ((True ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((p3 → p0) ∧ (False → False)) → ((True ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p6 p2 p5 : Prop)
theorem file54_34942 : ((((((p6 ∨ True) ∨ (p7 ∧ True)) → False) → (((True ∨ p6) ∨ (p2 ∨ True)) ∨ ((p6 → False) ∨ (p2 ∧ p5)))) → False) → False) := by
  intro assump_15
  have assump_25 : ((((p6 ∨ True) ∨ (p7 ∧ True)) → False) → (((True ∨ p6) ∨ (p2 ∨ True)) ∨ ((p6 → False) ∨ (p2 ∧ p5)))) := by
    intro assump_19
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_18 := assump_15 assump_25
  apply False.elim assump_18


variable (p6 p1 p4 p5 p0 : Prop)
theorem file54_35430 : (((((p0 ∨ p6) → False) ∧ ((p5 ∧ p5) ∧ (p0 → p4))) ∧ (((False → False) → False) ∧ ((p4 ∨ p1) ∨ (False ∨ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            cases assump_19
            case inl assump_22 =>
              cases assump_22
              case inl assump_24 =>
                have assump_60 : (False → False) := by
                  intro assump_30
                  apply False.elim assump_30
                let assump_29 := assump_18 assump_60
                apply False.elim assump_29
              case inr assump_25 =>
                have assump_61 : (False → False) := by
                  intro assump_40
                  apply False.elim assump_40
                let assump_39 := assump_18 assump_61
                apply False.elim assump_39
            case inr assump_23 =>
              cases assump_23
              case inl assump_46 =>
                apply False.elim assump_46
              case inr assump_47 =>
                have assump_62 : (False → False) := by
                  intro assump_54
                  apply False.elim assump_54
                let assump_53 := assump_18 assump_62
                apply False.elim assump_53


variable (p4 p5 p3 p2 p0 p1 p6 : Prop)
theorem file54_36967 : (((((p3 ∧ p2) → False) ∧ ((p3 ∧ True) ∨ (False → p1))) → False) → ((((p5 ∧ True) ∧ (p6 ∧ p4)) ∧ ((False ∧ p1) ∧ (p0 ∧ p5))) → False)) := by
  intro assump_9
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_14
        case intro assump_21 assump_22 =>
          cases assump_12
          case intro assump_27 assump_28 =>
            cases assump_27
            case intro assump_29 assump_30 =>
              apply False.elim assump_29


variable (p0 p2 p7 p3 p5 p6 p4 : Prop)
theorem file54_37630 : (((((p0 ∨ p4) → False) → False) ∨ (((p3 ∧ p0) ∧ (p3 → p6)) ∨ ((p5 ∧ False) → False))) → ((((p6 ∨ p4) → False) ∨ ((p6 ∧ p0) → (p4 ∧ p2))) → (((p7 ∨ p2) ∧ (False → False)) ∨ ((True → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      apply Or.inr
      intro assump_11
      have assump_87 : True := by
        apply True.intro
      let assump_14 := assump_11 assump_87
      apply False.elim assump_14
    case inr assump_8 =>
      cases assump_8
      case inl assump_18 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            apply Or.inr
            intro assump_30
            have assump_88 : True := by
              apply True.intro
            let assump_33 := assump_30 assump_88
            apply False.elim assump_33
      case inr assump_19 =>
        apply Or.inr
        intro assump_39
        have assump_89 : True := by
          apply True.intro
        let assump_42 := assump_39 assump_89
        apply False.elim assump_42
  case inr assump_4 =>
    cases assump_1
    case inl assump_48 =>
      apply Or.inr
      intro assump_52
      have assump_90 : True := by
        apply True.intro
      let assump_55 := assump_52 assump_90
      apply False.elim assump_55
    case inr assump_49 =>
      cases assump_49
      case inl assump_59 =>
        cases assump_59
        case intro assump_61 assump_62 =>
          cases assump_61
          case intro assump_63 assump_64 =>
            apply Or.inr
            intro assump_71
            have assump_91 : True := by
              apply True.intro
            let assump_74 := assump_71 assump_91
            apply False.elim assump_74
      case inr assump_60 =>
        apply Or.inr
        intro assump_80
        have assump_92 : True := by
          apply True.intro
        let assump_83 := assump_80 assump_92
        apply False.elim assump_83


variable (p0 p1 p3 p5 p7 p6 p4 : Prop)
theorem file54_39715 : (((((p0 ∧ p6) ∨ (p5 ∧ p7)) → ((p7 ∨ p4) ∨ (p0 ∧ p5))) → False) → ((((False ∨ p5) → (p7 ∨ p3)) ∨ ((p1 → False) → False)) ∨ (((p3 ∨ p4) → False) ∧ ((p4 ∨ p3) → False)))) := by
  intro assump_5
  apply Or.inl
  apply Or.inl
  intro assump_8
  cases assump_8
  case inl assump_9 =>
    apply False.elim assump_9
  case inr assump_10 =>
    have assump_35 : (((p0 ∧ p6) ∨ (p5 ∧ p7)) → ((p7 ∨ p4) ∨ (p0 ∧ p5))) := by
      intro assump_17
      cases assump_17
      case inl assump_18 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply Or.inr
          apply And.intro
          exact assump_20
          exact assump_10
      case inr assump_19 =>
        cases assump_19
        case intro assump_26 assump_27 =>
          apply Or.inl
          apply Or.inl
          exact assump_27
    let assump_16 := assump_5 assump_35
    apply False.elim assump_16


variable (p5 p7 p4 p1 p3 p2 p6 p0 : Prop)
theorem file54_40668 : (((((p7 ∧ p7) → False) → ((p5 ∨ True) ∨ (True → False))) ∨ (((True ∨ p6) ∨ (p1 ∨ True)) ∨ ((p1 → p1) ∨ (p5 → False)))) ∨ ((((p1 ∨ p4) → False) ∨ ((True ∨ p0) ∧ (p3 → True))) → (((p0 → True) ∨ (False ∧ p6)) ∧ ((p7 ∨ p6) ∧ (p2 ∨ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p1 p0 p3 p2 : Prop)
theorem file54_41059 : (((((True ∨ p0) ∨ (p2 → p1)) ∨ ((True ∨ p3) ∨ (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_8 : (((True ∨ p0) ∨ (p2 → p1)) ∨ ((True ∨ p3) ∨ (p0 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p6 p4 p3 p0 p7 : Prop)
theorem file54_41440 : (((((p3 → False) ∧ (True → p3)) → ((p3 → False) ∨ (p4 ∧ p7))) → False) → ((((p3 ∧ p3) ∨ (False → False)) → ((p0 → p6) → False)) ∧ (((p0 ∧ p0) ∧ (p1 → False)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      have assump_96 : (((p3 → False) ∧ (True → p3)) → ((p3 → False) ∨ (p4 ∧ p7))) := by
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          apply Or.inl
          intro assump_24
          have assump_97 : p3 := by
            exact assump_24
          let assump_30 := assump_18 assump_97
          apply False.elim assump_30
      let assump_16 := assump_1 assump_96
      apply False.elim assump_16
  case inr assump_7 =>
    have assump_98 : (((p3 → False) ∧ (True → p3)) → ((p3 → False) ∨ (p4 ∧ p7))) := by
      intro assump_42
      cases assump_42
      case intro assump_43 assump_44 =>
        apply Or.inl
        intro assump_49
        have assump_99 : p3 := by
          exact assump_49
        let assump_55 := assump_43 assump_99
        apply False.elim assump_55
    let assump_41 := assump_1 assump_98
    apply False.elim assump_41
  intro assump_62
  cases assump_62
  case intro assump_63 assump_64 =>
    cases assump_63
    case intro assump_65 assump_66 =>
      have assump_100 : (((p3 → False) ∧ (True → p3)) → ((p3 → False) ∨ (p4 ∧ p7))) := by
        intro assump_76
        cases assump_76
        case intro assump_77 assump_78 =>
          apply Or.inl
          intro assump_83
          have assump_101 : p3 := by
            exact assump_83
          let assump_89 := assump_77 assump_101
          apply False.elim assump_89
      let assump_75 := assump_1 assump_100
      apply False.elim assump_75


variable (p2 p1 p5 p4 p3 p6 : Prop)
theorem file54_43325 : (((((False ∧ p2) → False) ∨ ((p1 ∧ p3) → False)) → False) → ((((False → p4) → False) → False) ∨ (((p6 → p4) → (p2 ∧ p5)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (False → p4) := by
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p6 p4 p7 p3 : Prop)
theorem file54_43718 : (((((False → p4) → False) → ((p3 → p7) ∨ (True → p6))) → False) → False) := by
  intro assump_1
  have assump_22 : (((False → p4) → False) → ((p3 → p7) ∨ (True → p6))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_23 : (False → p4) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p1 p4 p3 p0 : Prop)
theorem file54_44235 : (((((p1 → p6) ∧ (p1 ∧ p3)) → ((p1 → p3) ∨ (p4 ∧ p0))) → (((p6 ∧ True) → (p6 → p6)) → False)) → False) := by
  intro assump_1
  have assump_33 : (((p1 → p6) ∧ (p1 ∧ p3)) → ((p1 → p3) ∨ (p4 ∧ p0))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_16
        exact assump_11
  let assump_4 := assump_1 assump_33
  have assump_34 : ((p6 ∧ True) → (p6 → p6)) := by
    intro assump_20
    intro assump_21
    cases assump_20
    case intro assump_24 assump_25 =>
      exact assump_24
  let assump_19 := assump_4 assump_34
  apply False.elim assump_19


variable (p6 p7 p5 p0 p1 : Prop)
theorem file54_44973 : ((((((True → p5) → (p5 → False)) ∧ ((p1 → p5) ∨ (p6 ∨ p7))) → False) ∧ ((((p0 ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p0 ∨ True) → False) → False) := by
      intro assump_9
      have assump_20 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p1 p2 p6 p0 p4 p7 p5 p3 : Prop)
theorem file54_45547 : (((((True → False) ∨ (True → False)) ∧ ((p7 → False) ∧ (p1 ∧ p1))) → (((p6 ∨ p1) → (p7 ∧ p3)) ∧ ((p0 ∨ p0) ∨ (p1 → False)))) ∨ ((((p5 → p1) → (p2 → p0)) → False) ∨ (((p7 → True) ∧ (True ∧ p4)) → ((p4 → p6) ∨ (p3 → p3))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            have assump_233 : True := by
              apply True.intro
            let assump_26 := assump_9 assump_233
            apply False.elim assump_26
      case inr assump_10 =>
        cases assump_8
        case intro assump_32 assump_33 =>
          cases assump_33
          case intro assump_36 assump_37 =>
            have assump_234 : True := by
              apply True.intro
            let assump_45 := assump_10 assump_234
            apply False.elim assump_45
  case inr assump_4 =>
    cases assump_1
    case intro assump_51 assump_52 =>
      cases assump_51
      case inl assump_53 =>
        cases assump_52
        case intro assump_57 assump_58 =>
          cases assump_58
          case intro assump_61 assump_62 =>
            have assump_235 : True := by
              apply True.intro
            let assump_70 := assump_53 assump_235
            apply False.elim assump_70
      case inr assump_54 =>
        cases assump_52
        case intro assump_76 assump_77 =>
          cases assump_77
          case intro assump_80 assump_81 =>
            have assump_236 : True := by
              apply True.intro
            let assump_89 := assump_54 assump_236
            apply False.elim assump_89
  cases assump_2
  case inl assump_93 =>
    cases assump_1
    case intro assump_97 assump_98 =>
      cases assump_97
      case inl assump_99 =>
        cases assump_98
        case intro assump_103 assump_104 =>
          cases assump_104
          case intro assump_107 assump_108 =>
            have assump_237 : True := by
              apply True.intro
            let assump_116 := assump_99 assump_237
            apply False.elim assump_116
      case inr assump_100 =>
        cases assump_98
        case intro assump_122 assump_123 =>
          cases assump_123
          case intro assump_126 assump_127 =>
            have assump_238 : True := by
              apply True.intro
            let assump_135 := assump_100 assump_238
            apply False.elim assump_135
  case inr assump_94 =>
    cases assump_1
    case intro assump_141 assump_142 =>
      cases assump_141
      case inl assump_143 =>
        cases assump_142
        case intro assump_147 assump_148 =>
          cases assump_148
          case intro assump_151 assump_152 =>
            have assump_239 : True := by
              apply True.intro
            let assump_160 := assump_143 assump_239
            apply False.elim assump_160
      case inr assump_144 =>
        cases assump_142
        case intro assump_166 assump_167 =>
          cases assump_167
          case intro assump_170 assump_171 =>
            have assump_240 : True := by
              apply True.intro
            let assump_179 := assump_144 assump_240
            apply False.elim assump_179
  cases assump_1
  case intro assump_183 assump_184 =>
    cases assump_183
    case inl assump_185 =>
      cases assump_184
      case intro assump_189 assump_190 =>
        cases assump_190
        case intro assump_193 assump_194 =>
          apply Or.inr
          intro assump_199
          have assump_241 : True := by
            apply True.intro
          let assump_206 := assump_185 assump_241
          apply False.elim assump_206
    case inr assump_186 =>
      cases assump_184
      case intro assump_212 assump_213 =>
        cases assump_213
        case intro assump_216 assump_217 =>
          apply Or.inr
          intro assump_222
          have assump_242 : True := by
            apply True.intro
          let assump_229 := assump_186 assump_242
          apply False.elim assump_229


variable (p0 p1 p6 p5 p3 p4 : Prop)
theorem file54_49806 : ((((((False ∧ p4) ∧ (p5 ∧ False)) ∧ ((p0 ∨ False) ∧ (p4 ∨ p1))) ∧ (((p3 ∨ p5) ∧ (True → False)) → False)) ∧ ((((True ∨ p6) → False) ∨ ((p6 ∧ p0) → False)) → False)) → False) := by
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


variable (p2 p7 p6 p0 p4 p1 p5 : Prop)
theorem file54_50402 : (((((True ∨ p6) → False) ∧ ((True → False) → (p6 ∧ False))) ∨ (((False → p5) → False) ∧ ((p2 → False) ∧ (p0 → p1)))) → ((((p4 → False) ∨ (p2 → p4)) ∧ ((p1 → False) ∧ (p7 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_10
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
    case inr assump_6 =>
      cases assump_4
      case intro assump_21 assump_22 =>
        cases assump_22
        case intro assump_25 assump_26 =>
          apply False.elim assump_26


variable (p3 p1 p2 : Prop)
theorem file54_51131 : ((((((True → False) → False) ∨ ((p3 ∧ p1) → False)) → (((False → False) → False) → ((False → False) ∨ (p2 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((True → False) → False) ∨ ((p3 ∧ p1) → False)) → (((False → False) → False) → ((False → False) ∨ (p2 ∧ p1)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    case inr assump_10 =>
      apply Or.inl
      intro assump_18
      apply False.elim assump_18
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p1 p4 p6 p2 p0 p3 : Prop)
theorem file54_51806 : (((((p2 → p4) → (p2 ∨ p0)) → False) ∧ (((False ∨ p4) ∨ (False → p6)) → False)) → ((((p6 → p3) ∨ (False ∨ p4)) ∨ ((p2 ∨ p6) → False)) → (((True → True) → (p1 ∨ p1)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_1
      case intro assump_12 assump_13 =>
        have assump_56 : ((False ∨ p4) ∨ (False → p6)) := by
          apply Or.inr
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_13 assump_56
        apply False.elim assump_18
    case inr assump_9 =>
      cases assump_9
      case inl assump_25 =>
        apply False.elim assump_25
      case inr assump_26 =>
        cases assump_1
        case intro assump_31 assump_32 =>
          have assump_57 : ((False ∨ p4) ∨ (False → p6)) := by
            apply Or.inl
            apply Or.inr
            exact assump_26
          let assump_37 := assump_32 assump_57
          apply False.elim assump_37
  case inr assump_7 =>
    cases assump_1
    case intro assump_43 assump_44 =>
      have assump_58 : ((False ∨ p4) ∨ (False → p6)) := by
        apply Or.inr
        intro assump_50
        apply False.elim assump_50
      let assump_49 := assump_44 assump_58
      apply False.elim assump_49


variable (p5 p7 p1 : Prop)
theorem file54_53183 : ((((((p5 ∧ True) → (p1 ∧ p7)) → False) → (((p5 ∨ True) → False) → ((p7 ∧ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p5 ∧ True) → (p1 ∧ p7)) → False) → (((p5 ∨ True) → False) → ((p7 ∧ p1) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      have assump_39 : ((p5 ∧ True) → (p1 ∧ p7)) := by
        intro assump_19
        apply And.intro
        cases assump_19
        case intro assump_20 assump_21 =>
          exact assump_9
        cases assump_19
        case intro assump_26 assump_27 =>
          exact assump_8
      let assump_18 := assump_5 assump_39
      apply False.elim assump_18
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p3 p4 p5 p7 : Prop)
theorem file54_54014 : ((((((True ∧ p5) ∨ (p4 → p7)) ∨ ((p5 ∨ p4) ∨ (p3 ∧ p7))) → (((True → p3) → (p5 → False)) → False)) ∧ ((((False → p7) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → p7) → False) → False) := by
      intro assump_9
      have assump_23 : (False → p7) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p0 p1 p7 p4 p3 p2 p5 : Prop)
theorem file54_54631 : (((((p0 ∨ p2) ∧ (p3 → p3)) ∨ ((p4 ∨ p1) ∧ (p7 ∧ p2))) → False) → ((((p4 → False) ∧ (p1 ∨ p5)) ∨ ((True ∨ p2) → False)) → (((p2 → p7) → False) → ((p3 → False) → (False ∨ p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_12
      case inl assump_15 =>
        have assump_70 : (p2 → p7) := by
          intro assump_25
          have assump_71 : (((p0 ∨ p2) ∧ (p3 → p3)) ∨ ((p4 ∨ p1) ∧ (p7 ∧ p2))) := by
            apply Or.inl
            apply And.intro
            apply Or.inr
            exact assump_25
            intro assump_30
            exact assump_30
          let assump_29 := assump_1 assump_71
          apply False.elim assump_29
        let assump_24 := assump_3 assump_70
        apply False.elim assump_24
      case inr assump_16 =>
        have assump_72 : (p2 → p7) := by
          intro assump_47
          have assump_73 : (((p0 ∨ p2) ∧ (p3 → p3)) ∨ ((p4 ∨ p1) ∧ (p7 ∧ p2))) := by
            apply Or.inl
            apply And.intro
            apply Or.inr
            exact assump_47
            intro assump_52
            exact assump_52
          let assump_51 := assump_1 assump_73
          apply False.elim assump_51
        let assump_46 := assump_3 assump_72
        apply False.elim assump_46
  case inr assump_10 =>
    have assump_74 : (True ∨ p2) := by
      apply Or.inl
      apply True.intro
    let assump_66 := assump_10 assump_74
    apply False.elim assump_66


variable (p6 p5 p2 p0 : Prop)
theorem file54_56240 : (((((True → False) → (p5 → False)) ∧ ((p6 ∧ False) → (False → False))) ∨ (((p5 ∧ p6) ∨ (p6 → p6)) ∨ ((p0 ∧ p0) → False))) → ((((False ∧ p5) ∧ (p2 ∧ p2)) ∧ ((False ∧ False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p4 p1 p0 p5 p6 p3 : Prop)
theorem file54_56731 : (((((p6 ∨ p6) ∨ (p1 ∧ p5)) → False) → (((p4 ∨ p1) → False) → ((True ∨ False) ∨ (p3 → False)))) ∨ ((((p0 → False) ∧ (False → p5)) ∧ ((p4 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p2 p7 p1 p0 p3 p4 p5 p6 : Prop)
theorem file54_57066 : (((((True → False) → False) ∧ ((p5 ∧ True) → (p4 ∨ True))) → (((False ∨ p0) → False) ∧ ((p6 → p2) → False))) → ((((p3 ∧ p0) → (p4 ∨ p0)) → ((p2 → p0) ∨ (p0 → p1))) ∧ (((p7 → False) ∨ (p4 ∨ True)) → ((True → False) → (p0 → p1))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply Or.inl
  intro assump_7
  have assump_118 : (((True → False) → False) ∧ ((p5 ∧ True) → (p4 ∨ True))) := by
    apply And.intro
    intro assump_12
    have assump_119 : True := by
      apply True.intro
    let assump_15 := assump_12 assump_119
    apply False.elim assump_15
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      apply Or.inr
      apply True.intro
  let assump_11 := assump_1 assump_118
  let assump_26 := And.right assump_11
  have assump_120 : (p6 → p2) := by
    intro assump_29
    exact assump_7
  let assump_28 := assump_26 assump_120
  apply False.elim assump_28
  intro assump_35
  intro assump_36
  intro assump_37
  cases assump_35
  case inl assump_42 =>
    have assump_121 : (((True → False) → False) ∧ ((p5 ∧ True) → (p4 ∨ True))) := by
      apply And.intro
      intro assump_49
      have assump_122 : True := by
        apply True.intro
      let assump_52 := assump_49 assump_122
      apply False.elim assump_52
      intro assump_56
      cases assump_56
      case intro assump_57 assump_58 =>
        apply Or.inr
        apply True.intro
    let assump_48 := assump_1 assump_121
    let assump_63 := And.left assump_48
    have assump_123 : (False ∨ p0) := by
      apply Or.inr
      exact assump_37
    let assump_64 := assump_63 assump_123
    apply False.elim assump_64
  case inr assump_43 =>
    cases assump_43
    case inl assump_68 =>
      have assump_124 : (((True → False) → False) ∧ ((p5 ∧ True) → (p4 ∨ True))) := by
        apply And.intro
        intro assump_75
        have assump_125 : True := by
          apply True.intro
        let assump_78 := assump_75 assump_125
        apply False.elim assump_78
        intro assump_82
        cases assump_82
        case intro assump_83 assump_84 =>
          apply Or.inl
          exact assump_68
      let assump_74 := assump_1 assump_124
      let assump_89 := And.left assump_74
      have assump_126 : (False ∨ p0) := by
        apply Or.inr
        exact assump_37
      let assump_90 := assump_89 assump_126
      apply False.elim assump_90
    case inr assump_69 =>
      have assump_127 : (((True → False) → False) ∧ ((p5 ∧ True) → (p4 ∨ True))) := by
        apply And.intro
        intro assump_99
        have assump_128 : True := by
          apply True.intro
        let assump_102 := assump_99 assump_128
        apply False.elim assump_102
        intro assump_106
        cases assump_106
        case intro assump_107 assump_108 =>
          apply Or.inr
          apply True.intro
      let assump_98 := assump_1 assump_127
      let assump_113 := And.left assump_98
      have assump_129 : (False ∨ p0) := by
        apply Or.inr
        exact assump_37
      let assump_114 := assump_113 assump_129
      apply False.elim assump_114


variable (p1 p3 p6 p5 p7 : Prop)
theorem file54_60210 : ((((((p5 ∧ False) ∧ (p7 → False)) ∧ ((p7 → True) ∧ (False → False))) ∧ (((p6 ∧ True) → False) ∧ ((False → p1) → False))) ∧ ((((False ∧ p7) → (p7 → False)) ∨ ((p6 → p5) → (p1 → p3))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15


variable (p5 p7 p1 p0 p2 p4 p6 : Prop)
theorem file54_60839 : (((((p0 ∨ p1) → False) → False) → (((p0 → p5) ∨ (p6 → p0)) → ((p1 ∧ True) → (p7 → p1)))) ∨ ((((p6 ∧ True) ∧ (False → False)) ∧ ((True → p2) → (p7 → p4))) → (((p4 ∨ p1) ∨ (p6 ∨ True)) → ((p0 ∧ True) → (False ∨ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_2
    case inl assump_13 =>
      exact assump_7
    case inr assump_14 =>
      exact assump_7


variable (p2 p6 p7 p1 p3 p0 p4 p5 : Prop)
theorem file54_61378 : ((((((p2 ∨ True) → False) → ((p6 ∨ p7) → False)) ∧ (((p1 → False) ∧ (p3 → False)) ∧ ((p3 → p4) ∨ (p0 → True)))) ∧ ((((p3 → p6) → (p4 ∨ True)) → False) ∨ (((False → p3) → (p1 ∨ p5)) ∧ ((p1 ∧ False) ∧ (p0 → p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case inl assump_16 =>
            cases assump_3
            case inl assump_20 =>
              have assump_68 : ((p3 → p6) → (p4 ∨ True)) := by
                intro assump_25
                apply Or.inr
                apply True.intro
              let assump_24 := assump_20 assump_68
              apply False.elim assump_24
            case inr assump_21 =>
              cases assump_21
              case intro assump_31 assump_32 =>
                cases assump_32
                case intro assump_35 assump_36 =>
                  cases assump_35
                  case intro assump_37 assump_38 =>
                    apply False.elim assump_38
          case inr assump_17 =>
            cases assump_3
            case inl assump_45 =>
              have assump_69 : ((p3 → p6) → (p4 ∨ True)) := by
                intro assump_50
                apply Or.inr
                apply True.intro
              let assump_49 := assump_45 assump_69
              apply False.elim assump_49
            case inr assump_46 =>
              cases assump_46
              case intro assump_56 assump_57 =>
                cases assump_57
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    apply False.elim assump_63


variable (p3 p6 p0 p4 p7 p1 : Prop)
theorem file54_63276 : (((((p6 → p0) → False) → ((p1 ∧ p3) → (p3 → p1))) → (((p0 → p4) ∧ (p4 → False)) ∧ ((p7 ∧ p4) ∧ (p4 ∧ False)))) → ((((True → False) ∨ (True ∧ p3)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_34 : (((p6 → p0) → False) → ((p1 ∧ p3) → (p3 → p1))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      exact assump_13
  let assump_7 := assump_1 assump_34
  let assump_21 := And.right assump_7
  let assump_25 := And.right assump_21
  let assump_29 := And.right assump_25
  apply False.elim assump_29


variable (p4 p5 p2 p7 p1 p0 p3 : Prop)
theorem file54_63936 : (((((p0 → False) → (p4 → p0)) → False) ∨ (((p1 ∧ p0) → (p0 ∧ p3)) ∧ ((p4 ∨ p5) → (p3 ∧ p7)))) → ((((p7 ∧ p0) → (p0 ∧ True)) ∧ ((False → False) ∧ (p3 ∧ p2))) → (((False ∧ p1) → False) ∧ ((p5 → False) → (p0 ∨ p2))))) := by
  intro assump_5
  intro assump_6
  apply And.intro
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8
  intro assump_12
  cases assump_6
  case intro assump_15 assump_16 =>
    cases assump_16
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        cases assump_5
        case inl assump_29 =>
          apply Or.inr
          exact assump_24
        case inr assump_30 =>
          cases assump_30
          case intro assump_33 assump_34 =>
            apply Or.inr
            exact assump_24


variable (p1 p3 p5 p0 p2 p7 p4 : Prop)
theorem file54_64816 : (((((p3 → True) ∨ (False → False)) ∨ ((p5 → False) → (p7 ∧ True))) ∨ (((p1 ∧ p2) → (True → False)) ∧ ((p7 ∧ p2) ∧ (p3 → False)))) ∨ ((((p4 ∨ p3) → False) ∧ ((p1 ∧ p1) ∧ (True ∨ p7))) ∧ (((p0 ∨ p3) → (p2 ∨ p3)) ∨ ((False → False) ∧ (p4 → p5))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply True.intro


variable (p1 p7 p3 p2 p6 : Prop)
theorem file54_65220 : ((((((p1 ∧ p2) → False) ∧ ((p7 → False) → False)) → (((False → False) ∧ (p3 → False)) → False)) ∧ ((((False ∨ p1) ∨ (p1 → False)) ∨ ((p6 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((False ∨ p1) ∨ (p1 → False)) ∨ ((p6 → False) → False)) := by
      apply Or.inl
      apply Or.inr
      intro assump_9
      have assump_21 : (((False ∨ p1) ∨ (p1 → False)) ∨ ((p6 → False) → False)) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        exact assump_9
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p0 p6 p7 p5 p3 p1 p4 p2 : Prop)
theorem file54_65994 : (((((p0 ∧ p0) ∨ (p4 ∧ p6)) → ((p0 ∧ p2) ∨ (p0 ∨ p2))) → (((p5 ∧ False) → False) ∨ ((p0 ∨ p1) ∧ (p5 ∧ p2)))) ∨ ((((p6 ∧ p7) → (p7 ∨ p2)) → ((p4 ∨ p3) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p3 p4 : Prop)
theorem file54_66362 : ((((((p3 → False) ∧ (p3 ∨ False)) → False) → (((p4 → False) → False) → ((False → False) → (True → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p3 → False) ∧ (p3 ∨ False)) → False) → (((p4 → False) → False) → ((False → False) → (True → True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p1 p4 p6 p2 p5 p3 p0 : Prop)
theorem file54_66868 : (((((p4 → True) ∨ (p0 ∨ p6)) ∧ ((False → False) ∨ (p4 → p3))) → False) → ((((p6 → False) ∨ (False → False)) ∧ ((p7 ∧ p2) ∨ (p7 ∧ p3))) ∧ (((p1 ∨ p4) ∧ (p5 ∧ True)) ∨ ((p3 ∨ p1) → (p7 ∧ p6))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_77 : (((p4 → True) ∨ (p0 ∨ p6)) ∧ ((False → False) ∨ (p4 → p3))) := by
    apply And.intro
    apply Or.inl
    intro assump_9
    apply True.intro
    apply Or.inl
    intro assump_10
    apply False.elim assump_10
  let assump_8 := assump_1 assump_77
  apply False.elim assump_8
  have assump_78 : (((p4 → True) ∨ (p0 ∨ p6)) ∧ ((False → False) ∨ (p4 → p3))) := by
    apply And.intro
    apply Or.inl
    intro assump_19
    apply True.intro
    apply Or.inl
    intro assump_20
    apply False.elim assump_20
  let assump_18 := assump_1 assump_78
  apply False.elim assump_18
  apply Or.inr
  intro assump_28
  apply And.intro
  cases assump_28
  case inl assump_29 =>
    have assump_79 : (((p4 → True) ∨ (p0 ∨ p6)) ∧ ((False → False) ∨ (p4 → p3))) := by
      apply And.intro
      apply Or.inl
      intro assump_35
      apply True.intro
      apply Or.inl
      intro assump_36
      apply False.elim assump_36
    let assump_34 := assump_1 assump_79
    apply False.elim assump_34
  case inr assump_30 =>
    have assump_80 : (((p4 → True) ∨ (p0 ∨ p6)) ∧ ((False → False) ∨ (p4 → p3))) := by
      apply And.intro
      apply Or.inl
      intro assump_46
      apply True.intro
      apply Or.inl
      intro assump_47
      apply False.elim assump_47
    let assump_45 := assump_1 assump_80
    apply False.elim assump_45
  cases assump_28
  case inl assump_53 =>
    have assump_81 : (((p4 → True) ∨ (p0 ∨ p6)) ∧ ((False → False) ∨ (p4 → p3))) := by
      apply And.intro
      apply Or.inl
      intro assump_59
      apply True.intro
      apply Or.inl
      intro assump_60
      apply False.elim assump_60
    let assump_58 := assump_1 assump_81
    apply False.elim assump_58
  case inr assump_54 =>
    have assump_82 : (((p4 → True) ∨ (p0 ∨ p6)) ∧ ((False → False) ∨ (p4 → p3))) := by
      apply And.intro
      apply Or.inl
      intro assump_70
      apply True.intro
      apply Or.inl
      intro assump_71
      apply False.elim assump_71
    let assump_69 := assump_1 assump_82
    apply False.elim assump_69


variable (p5 p7 p2 p4 p1 p0 p3 p6 : Prop)
theorem file54_69266 : (((((p1 ∨ True) → (p7 ∨ p2)) → ((p4 ∧ p1) → (p7 → p1))) ∨ (((p0 → p7) → (p0 → False)) → ((True ∨ p7) → (p4 ∨ True)))) ∨ ((((p5 ∧ p0) ∨ (p3 ∨ p5)) → False) → (((p3 ∧ p2) → (p6 → p0)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    exact assump_7


variable (p7 p5 p1 p3 p2 : Prop)
theorem file54_69673 : ((((((p3 ∨ True) → False) → False) ∨ (((p3 ∨ p5) ∨ (p2 → False)) → ((p7 → False) → (p1 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p3 ∨ True) → False) → False) ∨ (((p3 ∨ p5) ∨ (p2 → False)) → ((p7 → False) → (p1 ∧ p5)))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p0 p5 p6 p1 p3 : Prop)
theorem file54_70240 : (((((p7 ∨ p7) ∨ (p1 → p6)) → False) → (((p1 → p7) ∨ (p3 ∨ p7)) → ((p6 → False) ∨ (p1 ∧ p5)))) ∨ ((((p0 → False) → (p7 ∨ p1)) → ((False → p5) → (p3 ∧ True))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    have assump_49 : ((p7 ∨ p7) ∨ (p1 → p6)) := by
      apply Or.inr
      intro assump_14
      exact assump_9
    let assump_13 := assump_1 assump_49
    apply False.elim assump_13
  case inr assump_4 =>
    cases assump_4
    case inl assump_20 =>
      apply Or.inl
      intro assump_26
      have assump_50 : ((p7 ∨ p7) ∨ (p1 → p6)) := by
        apply Or.inr
        intro assump_31
        exact assump_26
      let assump_30 := assump_1 assump_50
      apply False.elim assump_30
    case inr assump_21 =>
      apply Or.inl
      intro assump_41
      have assump_51 : ((p7 ∨ p7) ∨ (p1 → p6)) := by
        apply Or.inl
        apply Or.inl
        exact assump_21
      let assump_45 := assump_1 assump_51
      apply False.elim assump_45


variable (p2 p7 p1 p3 : Prop)
theorem file54_71343 : ((((((False → False) ∨ (p7 → False)) ∨ ((p1 → p1) → False)) ∨ (((p7 → False) ∨ (p1 ∨ p2)) ∨ ((p3 ∨ p7) → (p1 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) ∨ (p7 → False)) ∨ ((p1 → p1) → False)) ∨ (((p7 → False) ∨ (p1 ∨ p2)) ∨ ((p3 ∨ p7) → (p1 ∧ p3)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p5 p1 p4 : Prop)
theorem file54_71862 : (((((False → False) → False) ∧ ((p3 → False) ∧ (p3 ∧ p1))) → False) ∨ ((((p4 → False) ∧ (p1 ∧ p3)) ∨ ((False ∧ p3) ∨ (True ∨ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_22 : p3 := by
          exact assump_10
        let assump_18 := assump_6 assump_22
        apply False.elim assump_18


variable (p4 p2 p5 p0 p7 p1 p6 : Prop)
theorem file54_72410 : (((((True ∨ p0) ∨ (True ∨ False)) ∨ ((p5 → p6) → (False ∨ p4))) → False) → ((((p5 ∧ p7) → False) ∧ ((False → p1) ∧ (p0 ∨ p2))) → (((p1 ∨ p1) ∧ (p7 → False)) ∨ ((p4 ∧ p1) ∨ (p2 ∨ p2))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        have assump_25 : (((True ∨ p0) ∨ (True ∨ False)) ∨ ((p5 → p6) → (False ∨ p4))) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_17 := assump_1 assump_25
        apply False.elim assump_17
      case inr assump_12 =>
        apply Or.inr
        apply Or.inr
        apply Or.inl
        exact assump_12


variable (p5 p6 p4 p2 p3 p7 p1 : Prop)
theorem file54_73237 : (((((False ∧ p6) ∧ (p5 ∧ False)) ∧ ((p2 ∨ p1) ∧ (p5 → False))) ∧ (((p2 ∨ p1) ∨ (p4 → False)) ∧ ((p3 → True) → (p6 → p4)))) → ((((p7 ∨ True) ∨ (False ∨ p7)) → False) → False)) := by
  intro assump_14
  intro assump_15
  cases assump_14
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          apply False.elim assump_24


variable (p2 p0 p3 p5 : Prop)
theorem file54_73785 : ((((((p0 ∧ p0) → (False → False)) ∧ ((True → False) → (p5 ∨ p3))) ∨ (((p0 → False) → (p2 ∨ p2)) → ((p3 → False) → (p5 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p0 ∧ p0) → (False → False)) ∧ ((True → False) → (p5 ∨ p3))) ∨ (((p0 → False) → (p2 ∨ p2)) → ((p3 → False) → (p5 ∨ p2)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    have assump_20 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p2 p3 p6 p5 p1 p7 p0 : Prop)
theorem file54_74484 : (((((p4 ∧ False) → (p4 → False)) ∨ ((p5 ∧ p0) → False)) ∨ (((p2 ∨ p7) → (p0 ∨ p2)) ∨ ((p0 → False) ∨ (p1 → False)))) ∨ ((((p3 ∨ True) → (p6 → p3)) ∨ ((p2 ∧ p7) → False)) ∨ (((True → p6) → (p5 ∧ p4)) ∧ ((p5 ∧ p4) ∧ (p5 → p1))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p3 p6 p4 p5 p1 p2 : Prop)
theorem file54_74938 : ((((((p1 ∧ False) → (p6 ∧ True)) ∧ ((p5 → False) → (False → False))) ∧ (((False ∨ p3) ∧ (p6 → p2)) → ((p1 ∨ False) → (p6 → p5)))) ∧ ((((False ∧ p5) ∨ (p4 ∧ p5)) → False) ∧ (((p6 ∨ p4) → (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          have assump_28 : ((p6 ∨ p4) → (False → False)) := by
            intro assump_21
            intro assump_22
            apply False.elim assump_22
          let assump_20 := assump_15 assump_28
          apply False.elim assump_20


variable (p2 p5 p6 p1 : Prop)
theorem file54_75710 : (((((p2 → False) ∧ (p1 ∧ p6)) → ((False → False) ∨ (p5 → False))) → (((p6 ∨ p5) → (p1 → p5)) ∧ ((True ∧ False) ∨ (p6 ∧ False)))) → False) := by
  intro assump_10
  have assump_45 : (((p2 → False) ∧ (p1 ∧ p6)) → ((False → False) ∨ (p5 → False))) := by
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_16
      case intro assump_19 assump_20 =>
        apply Or.inl
        intro assump_25
        apply False.elim assump_25
  let assump_13 := assump_10 assump_45
  let assump_28 := And.right assump_13
  cases assump_28
  case inl assump_31 =>
    cases assump_31
    case intro assump_33 assump_34 =>
      apply False.elim assump_34
  case inr assump_32 =>
    cases assump_32
    case intro assump_39 assump_40 =>
      apply False.elim assump_40


variable (p0 p2 p7 p6 : Prop)
theorem file54_76561 : ((((((True → p0) → False) → False) → (((True ∧ p7) ∨ (p2 → p6)) → ((False ∨ p6) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((True → p0) → False) → False) → (((True ∧ p7) ∨ (p2 → p6)) → ((False ∨ p6) → (False → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p3 p4 p5 p6 p1 : Prop)
theorem file54_77055 : ((((((p5 ∨ p4) → False) ∧ ((False → p1) → (p6 ∧ p4))) → (((p5 → False) → (p5 → False)) ∧ ((p6 ∧ p4) → (p3 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_56 : ((((p5 ∨ p4) → False) ∧ ((False → p1) → (p6 ∧ p4))) → (((p5 → False) → (p5 → False)) ∧ ((p6 ∧ p4) → (p3 ∨ False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      have assump_57 : (p5 ∨ p4) := by
        apply Or.inl
        exact assump_7
      let assump_25 := assump_12 assump_57
      apply False.elim assump_25
    intro assump_29
    cases assump_29
    case intro assump_30 assump_31 =>
      cases assump_5
      case intro assump_36 assump_37 =>
        have assump_58 : (p5 ∨ p4) := by
          apply Or.inr
          exact assump_31
        let assump_49 := assump_36 assump_58
        apply False.elim assump_49
  let assump_4 := assump_1 assump_56
  apply False.elim assump_4


variable (p0 p5 p4 p3 p1 p6 : Prop)
theorem file54_78082 : ((((((False → p5) ∨ (p6 → False)) ∨ ((p1 → False) ∨ (p4 ∨ True))) ∨ (((p6 ∧ p3) → (False → p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → p5) ∨ (p6 → False)) ∨ ((p1 → False) ∨ (p4 ∨ True))) ∨ (((p6 ∧ p3) → (False → p0)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p6 p0 p5 : Prop)
theorem file54_78577 : (((((False → p5) → (p6 → False)) → False) ∧ (((p4 ∨ p0) ∨ (p0 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : ((p4 ∨ p0) ∨ (p0 → False)) := by
      apply Or.inr
      intro assump_9
      have assump_21 : ((p4 ∨ p0) ∨ (p0 → False)) := by
        apply Or.inl
        apply Or.inr
        exact assump_9
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p4 p5 p2 : Prop)
theorem file54_79152 : (((((p2 ∧ p4) ∧ (p4 → False)) → ((p2 → False) ∧ (p5 ∧ p2))) → False) → False) := by
  intro assump_1
  have assump_50 : (((p2 ∧ p4) ∧ (p4 → False)) → ((p2 → False) ∧ (p5 ∧ p2))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_51 : p4 := by
          exact assump_12
        let assump_19 := assump_10 assump_51
        apply False.elim assump_19
    apply And.intro
    cases assump_5
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        have assump_52 : p4 := by
          exact assump_26
        let assump_33 := assump_24 assump_52
        apply False.elim assump_33
    cases assump_5
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        exact assump_39
  let assump_4 := assump_1 assump_50
  apply False.elim assump_4


variable (p1 p0 p2 p7 p4 : Prop)
theorem file54_80195 : ((((((p7 ∧ p7) ∨ (p2 ∨ p2)) ∨ ((True ∨ p2) → False)) → (((True → False) → (p0 → False)) ∨ ((p4 ∧ p4) ∧ (p1 → p0)))) → False) → False) := by
  intro assump_1
  have assump_67 : ((((p7 ∧ p7) ∨ (p2 ∨ p2)) ∨ ((True ∨ p2) → False)) → (((True → False) → (p0 → False)) ∨ ((p4 ∧ p4) ∧ (p1 → p0)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_16
          intro assump_17
          have assump_68 : True := by
            apply True.intro
          let assump_22 := assump_16 assump_68
          apply False.elim assump_22
      case inr assump_9 =>
        cases assump_9
        case inl assump_26 =>
          apply Or.inl
          intro assump_30
          intro assump_31
          have assump_69 : True := by
            apply True.intro
          let assump_36 := assump_30 assump_69
          apply False.elim assump_36
        case inr assump_27 =>
          apply Or.inl
          intro assump_42
          intro assump_43
          have assump_70 : True := by
            apply True.intro
          let assump_48 := assump_42 assump_70
          apply False.elim assump_48
    case inr assump_7 =>
      apply Or.inl
      intro assump_54
      intro assump_55
      have assump_71 : True := by
        apply True.intro
      let assump_60 := assump_54 assump_71
      apply False.elim assump_60
  let assump_4 := assump_1 assump_67
  apply False.elim assump_4


variable (p0 p4 : Prop)
theorem file54_81791 : (((((p4 ∨ p0) ∧ (True ∧ False)) → False) → False) → False) := by
  intro assump_16
  have assump_44 : (((p4 ∨ p0) ∧ (True ∧ False)) → False) := by
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      cases assump_21
      case inl assump_23 =>
        cases assump_22
        case intro assump_27 assump_28 =>
          apply False.elim assump_28
      case inr assump_24 =>
        cases assump_22
        case intro assump_35 assump_36 =>
          apply False.elim assump_36
  let assump_19 := assump_16 assump_44
  apply False.elim assump_19


variable (p6 p0 p2 p4 p1 p3 p7 p5 : Prop)
theorem file54_82434 : (((((True → False) ∧ (p7 ∨ p1)) ∧ ((p1 → False) → (p3 ∧ True))) ∨ (((p4 ∨ p6) ∨ (p3 → False)) ∨ ((p0 ∨ p6) → False))) → ((((p3 → True) ∨ (p2 ∧ True)) ∨ ((p3 → False) ∨ (p6 → p3))) ∧ (((p3 ∧ p7) ∨ (True → p3)) → ((p6 ∧ False) → (p5 → True))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          apply Or.inl
          apply Or.inl
          intro assump_16
          apply True.intro
        case inr assump_11 =>
          apply Or.inl
          apply Or.inl
          intro assump_21
          apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_22 =>
      cases assump_22
      case inl assump_24 =>
        cases assump_24
        case inl assump_26 =>
          apply Or.inl
          apply Or.inl
          intro assump_30
          apply True.intro
        case inr assump_27 =>
          apply Or.inl
          apply Or.inl
          intro assump_33
          apply True.intro
      case inr assump_25 =>
        apply Or.inl
        apply Or.inl
        intro assump_36
        apply True.intro
    case inr assump_23 =>
      apply Or.inl
      apply Or.inl
      intro assump_39
      apply True.intro
  intro assump_40
  intro assump_41
  intro assump_42
  apply True.intro


variable (p6 p2 p7 : Prop)
theorem file54_83905 : (((((True → False) → (p6 → p2)) ∨ ((p7 ∨ p7) → (True → False))) → False) → False) := by
  intro assump_1
  have assump_18 : (((True → False) → (p6 → p2)) ∨ ((p7 ∨ p7) → (True → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p1 p6 p3 p7 p4 p0 p5 : Prop)
theorem file54_84409 : (((((p6 ∨ p5) ∧ (True ∧ p7)) ∧ ((p3 → False) → (p2 ∧ p3))) ∨ (((p5 ∨ p5) ∧ (p1 → False)) → ((p5 → False) → (True ∧ p7)))) ∨ ((((False → False) ∨ (p2 ∨ p2)) ∧ ((p7 ∨ p0) → (p6 → False))) ∧ (((p3 ∨ p7) → (p4 ∨ p6)) → False))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  apply And.intro
  apply True.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_29 : p5 := by
        exact assump_7
      let assump_15 := assump_2 assump_29
      apply False.elim assump_15
    case inr assump_8 =>
      have assump_30 : p5 := by
        exact assump_8
      let assump_25 := assump_2 assump_30
      apply False.elim assump_25


variable (p0 p4 p6 p5 p2 p1 p7 p3 : Prop)
theorem file54_85186 : (((((True ∧ False) ∧ (False ∨ False)) → ((p2 → False) ∨ (p5 → p0))) ∨ (((p1 ∧ p7) → False) ∨ ((p7 ∧ p0) → (p1 ∧ p1)))) ∨ ((((False ∧ p3) ∨ (p6 → p5)) ∧ ((True → False) → False)) → (((p4 → False) ∧ (p5 → False)) ∨ ((p5 ∨ p0) ∧ (False ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      apply False.elim assump_15


variable (p2 p3 p6 p4 p7 p5 p1 : Prop)
theorem file54_85691 : ((((((p5 → False) → (True → p6)) ∨ ((p4 ∨ True) ∨ (p2 → False))) ∨ (((p1 → p2) → False) → ((p7 → False) → False))) ∧ ((((p2 → p3) ∧ (p2 → p3)) → False) ∧ (((True ∧ False) → (p6 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          have assump_82 : ((True ∧ False) → (p6 → True)) := by
            intro assump_17
            intro assump_18
            apply True.intro
          let assump_16 := assump_11 assump_82
          apply False.elim assump_16
      case inr assump_7 =>
        cases assump_7
        case inl assump_22 =>
          cases assump_22
          case inl assump_24 =>
            cases assump_3
            case intro assump_28 assump_29 =>
              have assump_83 : ((True ∧ False) → (p6 → True)) := by
                intro assump_35
                intro assump_36
                apply True.intro
              let assump_34 := assump_29 assump_83
              apply False.elim assump_34
          case inr assump_25 =>
            cases assump_3
            case intro assump_42 assump_43 =>
              have assump_84 : ((True ∧ False) → (p6 → True)) := by
                intro assump_49
                intro assump_50
                apply True.intro
              let assump_48 := assump_43 assump_84
              apply False.elim assump_48
        case inr assump_23 =>
          cases assump_3
          case intro assump_56 assump_57 =>
            have assump_85 : ((True ∧ False) → (p6 → True)) := by
              intro assump_63
              intro assump_64
              apply True.intro
            let assump_62 := assump_57 assump_85
            apply False.elim assump_62
    case inr assump_5 =>
      cases assump_3
      case intro assump_70 assump_71 =>
        have assump_86 : ((True ∧ False) → (p6 → True)) := by
          intro assump_77
          intro assump_78
          apply True.intro
        let assump_76 := assump_71 assump_86
        apply False.elim assump_76


variable (p6 p1 p7 p4 p0 : Prop)
theorem file54_87899 : (((((p7 → False) → (p0 → p4)) ∧ ((p0 ∨ p6) → (True → False))) ∧ (((False → False) ∨ (False ∧ p7)) → False)) → ((((False ∧ p6) ∧ (p1 ∨ p4)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_22 : ((False → False) ∨ (False ∧ p7)) := by
        apply Or.inl
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_6 assump_22
      apply False.elim assump_15


variable (p3 p4 p2 p1 p7 p6 : Prop)
theorem file54_88480 : ((((((p3 → p6) ∨ (p1 → True)) → False) → (((p7 → False) ∧ (p6 → False)) → ((p4 ∧ p7) → (p2 → False)))) ∧ ((((p6 → False) ∧ (p2 ∧ p4)) → False) ∧ (((p6 ∨ False) ∨ (False ∧ p1)) ∧ ((p4 → p7) ∧ (False ∧ True))))) → False) := by
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
            cases assump_11
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                apply False.elim assump_22
          case inr assump_15 =>
            apply False.elim assump_15
        case inr assump_13 =>
          cases assump_13
          case intro assump_28 assump_29 =>
            apply False.elim assump_28


variable (p3 p4 p7 : Prop)
theorem file54_89457 : ((((((p4 → True) → False) → False) ∨ (((p7 ∨ p3) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p4 → True) → False) → False) ∨ (((p7 ∨ p3) → False) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_17 : (p4 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p7 p2 p5 p3 p1 p4 : Prop)
theorem file54_89973 : (((((False ∨ p2) ∧ (p3 ∨ p5)) ∧ ((p1 ∧ p2) ∧ (p5 → p3))) → False) → ((((p2 → False) ∨ (p3 ∧ p0)) ∧ ((p4 → False) → (p0 ∨ p7))) → (((p4 ∧ False) ∧ (p1 → False)) → ((p3 ∨ p0) ∧ (p1 ∨ False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  cases assump_3
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      apply False.elim assump_15


variable (p6 p4 p5 p1 p3 : Prop)
theorem file54_90579 : ((((((p6 → p1) ∧ (p4 → p4)) ∧ ((p4 → False) → False)) → (((p3 ∨ p6) → False) → ((p5 ∧ p4) ∨ (True ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p6 → p1) ∧ (p4 → p4)) ∧ ((p4 → False) → False)) → (((p3 ∨ p6) → False) → ((p5 ∧ p4) ∨ (True ∨ p5)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inr
        apply Or.inl
        apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p6 p1 p5 p7 p3 : Prop)
theorem file54_91204 : (((((p6 ∨ p2) ∨ (p1 ∨ False)) ∨ ((True ∧ p6) → False)) → False) → ((((p7 ∧ p6) → (p3 → False)) → False) ∨ (((False ∧ p7) ∨ (p2 → True)) ∨ ((p2 ∧ p1) ∧ (p5 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_25 : (((p6 ∨ p2) ∨ (p1 ∨ False)) ∨ ((True ∧ p6) → False)) := by
    apply Or.inr
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      have assump_26 : (((p6 ∨ p2) ∨ (p1 ∨ False)) ∨ ((True ∧ p6) → False)) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact assump_11
      let assump_18 := assump_1 assump_26
      apply False.elim assump_18
  let assump_8 := assump_1 assump_25
  apply False.elim assump_8


variable (p4 p3 : Prop)
theorem file54_91955 : (((((True → False) → False) ∨ ((p4 ∧ p3) → (False ∧ p3))) → False) → False) := by
  intro assump_1
  have assump_15 : (((True → False) → False) ∨ ((p4 ∧ p3) → (False ∧ p3))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p6 p4 p2 p1 p0 : Prop)
theorem file54_92420 : (((((p6 → p5) ∨ (True ∨ p2)) → ((p5 ∧ p2) → (p2 ∨ p4))) → False) → ((((p6 ∧ p0) → False) ∨ ((p1 → False) ∧ (p2 ∧ p1))) → False)) := by
  intro assump_44
  intro assump_45
  cases assump_45
  case inl assump_46 =>
    have assump_108 : (((p6 → p5) ∨ (True ∨ p2)) → ((p5 ∧ p2) → (p2 ∨ p4))) := by
      intro assump_53
      intro assump_54
      cases assump_54
      case intro assump_55 assump_56 =>
        cases assump_53
        case inl assump_61 =>
          apply Or.inl
          exact assump_56
        case inr assump_62 =>
          cases assump_62
          case inl assump_65 =>
            apply Or.inl
            exact assump_56
          case inr assump_66 =>
            apply Or.inl
            exact assump_66
    let assump_52 := assump_44 assump_108
    apply False.elim assump_52
  case inr assump_47 =>
    cases assump_47
    case intro assump_74 assump_75 =>
      cases assump_75
      case intro assump_78 assump_79 =>
        have assump_109 : (((p6 → p5) ∨ (True ∨ p2)) → ((p5 ∧ p2) → (p2 ∨ p4))) := by
          intro assump_87
          intro assump_88
          cases assump_88
          case intro assump_89 assump_90 =>
            cases assump_87
            case inl assump_95 =>
              apply Or.inl
              exact assump_90
            case inr assump_96 =>
              cases assump_96
              case inl assump_99 =>
                apply Or.inl
                exact assump_90
              case inr assump_100 =>
                apply Or.inl
                exact assump_100
        let assump_86 := assump_44 assump_109
        apply False.elim assump_86


variable (p0 p3 p5 p1 p6 p7 p2 p4 : Prop)
theorem file54_94101 : (((((p5 → p5) → False) → ((p3 → p4) → False)) ∨ (((p6 → p3) ∧ (p4 ∧ p1)) ∧ ((p0 → False) ∧ (True ∨ p3)))) ∨ ((((p2 ∧ p3) ∧ (p1 → p1)) ∨ ((True → p1) → (p6 ∨ True))) ∨ (((p6 → p7) → (p3 → p1)) ∧ ((p2 → False) ∨ (p4 ∨ False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  have assump_18 : (p5 → p5) := by
    intro assump_12
    exact assump_12
  let assump_11 := assump_5 assump_18
  apply False.elim assump_11


variable (p6 p2 p5 p4 p0 : Prop)
theorem file54_94597 : (((((p0 → True) → False) ∨ ((p0 ∨ False) → False)) → False) → ((((p5 → False) ∧ (True → p6)) ∧ ((p2 → p4) → (p5 → False))) → (((p6 ∨ p2) ∧ (p6 ∨ True)) ∨ ((p0 ∨ False) → (p4 ∨ True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply Or.inr
      intro assump_15
      cases assump_15
      case inl assump_16 =>
        apply Or.inr
        apply True.intro
      case inr assump_17 =>
        apply False.elim assump_17


variable (p0 p4 p3 p5 p6 p2 p1 p7 : Prop)
theorem file54_95195 : ((((((p1 ∧ p4) → False) ∧ ((p6 ∨ p7) ∧ (p2 ∧ False))) ∧ (((p2 → p4) ∨ (True ∨ p7)) → ((p5 ∧ True) ∧ (False ∧ False)))) ∧ ((((p3 ∨ p2) ∨ (p6 → False)) → ((p3 ∨ p1) ∧ (False ∧ p0))) ∧ (((p3 ∧ p7) ∨ (p6 → p7)) ∧ ((p7 ∨ p6) → False)))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_19
            case intro assump_24 assump_25 =>
              apply False.elim assump_25
          case inr assump_21 =>
            cases assump_19
            case intro assump_32 assump_33 =>
              apply False.elim assump_33


variable (p7 p5 p1 p6 p0 p3 p2 : Prop)
theorem file54_96081 : ((((((p5 ∧ False) ∨ (p5 ∧ p2)) ∨ ((p6 ∨ p7) ∨ (p6 → False))) ∨ (((p1 ∨ p7) ∨ (p0 ∧ p2)) → ((p3 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p5 ∧ False) ∨ (p5 ∧ p2)) ∨ ((p6 ∨ p7) ∨ (p6 → False))) ∨ (((p1 ∨ p7) ∨ (p0 ∧ p2)) → ((p3 → False) → False))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_5
    have assump_17 : ((((p5 ∧ False) ∨ (p5 ∧ p2)) ∨ ((p6 ∨ p7) ∨ (p6 → False))) ∨ (((p1 ∨ p7) ∨ (p0 ∧ p2)) → ((p3 → False) → False))) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p4 p2 p0 p3 p5 : Prop)
theorem file54_96876 : ((((((False → False) ∧ (p4 ∧ p3)) → False) ∧ (((p6 ∨ True) → (True → False)) → False)) ∧ ((((p0 ∧ p5) → (p2 ∨ p5)) ∧ ((True → True) ∨ (p0 → False))) → (((p2 ∨ True) ∨ (p4 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_25 : (((p0 ∧ p5) → (p2 ∨ p5)) ∧ ((True → True) ∨ (p0 → False))) := by
        apply And.intro
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply Or.inr
          exact assump_15
        apply Or.inl
        intro assump_20
        apply True.intro
      let assump_12 := assump_3 assump_25
      have assump_26 : ((p2 ∨ True) ∨ (p4 → False)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_21 := assump_12 assump_26
      apply False.elim assump_21


