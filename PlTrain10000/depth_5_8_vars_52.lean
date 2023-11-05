variable (p5 p6 p2 p3 p7 p1 p0 p4 : Prop)
theorem file52_50 : (((((p3 ∨ p3) ∨ (p3 → True)) ∧ ((p2 ∧ p0) ∧ (True → False))) → (((p5 ∧ False) ∨ (p1 → p4)) → ((p7 ∨ False) ∧ (True → False)))) ∨ ((((p6 ∨ p5) → False) → ((False ∧ p1) ∧ (p0 ∨ False))) → (((p6 ∧ p0) ∨ (p6 ∨ p5)) ∧ ((True → False) → (p4 → p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6
  case inr assump_4 =>
    cases assump_1
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_15
        case inl assump_17 =>
          cases assump_14
          case intro assump_21 assump_22 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              have assump_134 : True := by
                apply True.intro
              let assump_31 := assump_22 assump_134
              apply False.elim assump_31
        case inr assump_18 =>
          cases assump_14
          case intro assump_37 assump_38 =>
            cases assump_37
            case intro assump_39 assump_40 =>
              have assump_135 : True := by
                apply True.intro
              let assump_47 := assump_38 assump_135
              apply False.elim assump_47
      case inr assump_16 =>
        cases assump_14
        case intro assump_53 assump_54 =>
          cases assump_53
          case intro assump_55 assump_56 =>
            have assump_136 : True := by
              apply True.intro
            let assump_63 := assump_54 assump_136
            apply False.elim assump_63
  intro assump_67
  cases assump_2
  case inl assump_70 =>
    cases assump_70
    case intro assump_72 assump_73 =>
      apply False.elim assump_73
  case inr assump_71 =>
    cases assump_1
    case intro assump_80 assump_81 =>
      cases assump_80
      case inl assump_82 =>
        cases assump_82
        case inl assump_84 =>
          cases assump_81
          case intro assump_88 assump_89 =>
            cases assump_88
            case intro assump_90 assump_91 =>
              have assump_137 : True := by
                apply True.intro
              let assump_98 := assump_89 assump_137
              apply False.elim assump_98
        case inr assump_85 =>
          cases assump_81
          case intro assump_104 assump_105 =>
            cases assump_104
            case intro assump_106 assump_107 =>
              have assump_138 : True := by
                apply True.intro
              let assump_114 := assump_105 assump_138
              apply False.elim assump_114
      case inr assump_83 =>
        cases assump_81
        case intro assump_120 assump_121 =>
          cases assump_120
          case intro assump_122 assump_123 =>
            have assump_139 : True := by
              apply True.intro
            let assump_130 := assump_121 assump_139
            apply False.elim assump_130


variable (p0 p1 p5 p2 p4 p6 p7 : Prop)
theorem file52_3055 : (((((False ∧ p5) ∧ (p4 ∨ p6)) ∨ ((False → False) ∨ (p4 → False))) ∨ (((p0 → p2) → False) ∧ ((p6 ∧ True) → (p1 → p2)))) ∨ ((((p7 → p6) → (p6 ∧ p7)) → ((False ∧ False) → (p1 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p4 : Prop)
theorem file52_3404 : ((((((p4 ∧ False) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p4 ∧ False) → False) → False) → False) := by
    intro assump_5
    have assump_23 : ((p4 ∧ False) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p3 p6 p5 p0 p4 p7 : Prop)
theorem file52_3938 : (((((False → p6) ∧ (False ∨ False)) → False) ∨ (((p5 ∨ p7) → (p5 → p0)) → False)) ∨ ((((True → p5) ∨ (p4 ∧ p0)) → False) ∧ (((False → p7) ∨ (False → p0)) ∧ ((p4 → p3) ∨ (p0 → False))))) := by
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


variable (p2 p6 p5 p1 p0 p4 : Prop)
theorem file52_4421 : ((((((p0 → False) ∧ (True → False)) → ((p2 → p0) ∨ (p0 ∧ p0))) ∨ (((p4 ∧ True) → (p6 → False)) ∧ ((p1 ∨ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p0 → False) ∧ (True → False)) → ((p2 → p0) ∨ (p0 ∧ p0))) ∨ (((p4 ∧ True) → (p6 → False)) ∧ ((p1 ∨ p5) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      have assump_24 : True := by
        apply True.intro
      let assump_16 := assump_7 assump_24
      apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p4 p1 p2 : Prop)
theorem file52_5105 : (((((p1 → p1) ∧ (p2 → p2)) → False) → False) ∨ ((((p2 ∨ p4) → False) ∧ ((p1 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_15
  have assump_28 : ((p1 → p1) ∧ (p2 → p2)) := by
    apply And.intro
    intro assump_19
    exact assump_19
    intro assump_22
    exact assump_22
  let assump_18 := assump_15 assump_28
  apply False.elim assump_18


variable (p3 p6 p1 p5 p2 p7 p0 : Prop)
theorem file52_5529 : (((((p7 ∨ p1) ∧ (p6 ∧ p5)) → ((True ∨ p3) ∨ (p6 ∧ p7))) ∧ (((p0 → False) ∨ (p6 → p0)) → ((True ∧ p1) → (p2 ∨ True)))) ∨ ((((p1 → False) → (p6 ∨ p7)) → False) ∨ (((p1 ∧ p2) → (p6 ∧ p1)) ∧ ((True ∨ p7) ∨ (True ∨ p3))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      cases assump_3
      case intro assump_16 assump_17 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
  intro assump_22
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    cases assump_22
    case inl assump_30 =>
      apply Or.inr
      apply True.intro
    case inr assump_31 =>
      apply Or.inr
      apply True.intro


variable (p6 p0 p4 : Prop)
theorem file52_6474 : (((((p4 → True) ∨ (p6 ∨ p6)) ∨ ((False ∨ p0) → (True ∨ False))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p4 → True) ∨ (p6 ∨ p6)) ∨ ((False ∨ p0) → (True ∨ False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p4 p1 p0 p7 p5 p2 : Prop)
theorem file52_6863 : (((((p1 ∧ p4) ∨ (p1 → False)) ∧ ((p4 ∧ False) ∧ (p0 ∧ p2))) ∧ (((False ∨ p1) → False) → False)) → ((((True → False) → (p7 → False)) → ((False ∧ True) → (p7 ∨ False))) → (((p1 ∨ True) ∨ (p1 → p5)) → ((p2 ∨ p7) ∧ (True ∧ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_1
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_15
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  apply False.elim assump_27
          case inr assump_17 =>
            cases assump_15
            case intro assump_34 assump_35 =>
              cases assump_34
              case intro assump_36 assump_37 =>
                apply False.elim assump_37
    case inr assump_7 =>
      cases assump_1
      case intro assump_46 assump_47 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          cases assump_48
          case inl assump_50 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_49
              case intro assump_58 assump_59 =>
                cases assump_58
                case intro assump_60 assump_61 =>
                  apply False.elim assump_61
          case inr assump_51 =>
            cases assump_49
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                apply False.elim assump_71
  case inr assump_5 =>
    cases assump_1
    case intro assump_80 assump_81 =>
      cases assump_80
      case intro assump_82 assump_83 =>
        cases assump_82
        case inl assump_84 =>
          cases assump_84
          case intro assump_86 assump_87 =>
            cases assump_83
            case intro assump_92 assump_93 =>
              cases assump_92
              case intro assump_94 assump_95 =>
                apply False.elim assump_95
        case inr assump_85 =>
          cases assump_83
          case intro assump_102 assump_103 =>
            cases assump_102
            case intro assump_104 assump_105 =>
              apply False.elim assump_105
  apply And.intro
  apply True.intro
  cases assump_3
  case inl assump_110 =>
    cases assump_110
    case inl assump_112 =>
      cases assump_1
      case intro assump_118 assump_119 =>
        cases assump_118
        case intro assump_120 assump_121 =>
          cases assump_120
          case inl assump_122 =>
            cases assump_122
            case intro assump_124 assump_125 =>
              cases assump_121
              case intro assump_130 assump_131 =>
                cases assump_130
                case intro assump_132 assump_133 =>
                  apply False.elim assump_133
          case inr assump_123 =>
            cases assump_121
            case intro assump_140 assump_141 =>
              cases assump_140
              case intro assump_142 assump_143 =>
                apply False.elim assump_143
    case inr assump_113 =>
      cases assump_1
      case intro assump_152 assump_153 =>
        cases assump_152
        case intro assump_154 assump_155 =>
          cases assump_154
          case inl assump_156 =>
            cases assump_156
            case intro assump_158 assump_159 =>
              cases assump_155
              case intro assump_164 assump_165 =>
                cases assump_164
                case intro assump_166 assump_167 =>
                  apply False.elim assump_167
          case inr assump_157 =>
            cases assump_155
            case intro assump_174 assump_175 =>
              cases assump_174
              case intro assump_176 assump_177 =>
                apply False.elim assump_177
  case inr assump_111 =>
    cases assump_1
    case intro assump_186 assump_187 =>
      cases assump_186
      case intro assump_188 assump_189 =>
        cases assump_188
        case inl assump_190 =>
          cases assump_190
          case intro assump_192 assump_193 =>
            cases assump_189
            case intro assump_198 assump_199 =>
              cases assump_198
              case intro assump_200 assump_201 =>
                apply False.elim assump_201
        case inr assump_191 =>
          cases assump_189
          case intro assump_208 assump_209 =>
            cases assump_208
            case intro assump_210 assump_211 =>
              apply False.elim assump_211


variable (p3 p7 p4 p6 p5 p2 p0 p1 : Prop)
theorem file52_11693 : ((((((p6 → False) → (p6 → False)) → False) ∧ (((False ∨ p0) ∨ (p1 → False)) ∧ ((p1 ∨ p4) ∧ (p5 ∧ p5)))) ∨ ((((p7 → False) → False) → False) ∧ (((False → p2) → False) ∧ ((p2 → False) ∨ (p5 ∨ p3))))) → False) := by
  intro assump_20
  cases assump_20
  case inl assump_21 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        cases assump_27
        case inl assump_29 =>
          cases assump_29
          case inl assump_31 =>
            apply False.elim assump_31
          case inr assump_32 =>
            cases assump_28
            case intro assump_37 assump_38 =>
              cases assump_37
              case inl assump_39 =>
                cases assump_38
                case intro assump_43 assump_44 =>
                  have assump_182 : ((p6 → False) → (p6 → False)) := by
                    intro assump_54
                    intro assump_55
                    have assump_183 : p6 := by
                      exact assump_55
                    let assump_60 := assump_54 assump_183
                    apply False.elim assump_60
                  let assump_53 := assump_23 assump_182
                  apply False.elim assump_53
              case inr assump_40 =>
                cases assump_38
                case intro assump_69 assump_70 =>
                  have assump_184 : ((p6 → False) → (p6 → False)) := by
                    intro assump_80
                    intro assump_81
                    have assump_185 : p6 := by
                      exact assump_81
                    let assump_86 := assump_80 assump_185
                    apply False.elim assump_86
                  let assump_79 := assump_23 assump_184
                  apply False.elim assump_79
        case inr assump_30 =>
          cases assump_28
          case intro assump_95 assump_96 =>
            cases assump_95
            case inl assump_97 =>
              cases assump_96
              case intro assump_101 assump_102 =>
                have assump_186 : p1 := by
                  exact assump_97
                let assump_110 := assump_30 assump_186
                apply False.elim assump_110
            case inr assump_98 =>
              cases assump_96
              case intro assump_116 assump_117 =>
                have assump_187 : ((p6 → False) → (p6 → False)) := by
                  intro assump_127
                  intro assump_128
                  have assump_188 : p6 := by
                    exact assump_128
                  let assump_133 := assump_127 assump_188
                  apply False.elim assump_133
                let assump_126 := assump_23 assump_187
                apply False.elim assump_126
  case inr assump_22 =>
    cases assump_22
    case intro assump_140 assump_141 =>
      cases assump_141
      case intro assump_144 assump_145 =>
        cases assump_145
        case inl assump_148 =>
          have assump_189 : (False → p2) := by
            intro assump_154
            apply False.elim assump_154
          let assump_153 := assump_144 assump_189
          apply False.elim assump_153
        case inr assump_149 =>
          cases assump_149
          case inl assump_160 =>
            have assump_190 : (False → p2) := by
              intro assump_166
              apply False.elim assump_166
            let assump_165 := assump_144 assump_190
            apply False.elim assump_165
          case inr assump_161 =>
            have assump_191 : (False → p2) := by
              intro assump_176
              apply False.elim assump_176
            let assump_175 := assump_144 assump_191
            apply False.elim assump_175


variable (p5 p0 p6 p3 p4 p1 p7 : Prop)
theorem file52_15460 : ((((((p5 → p3) → (p7 → False)) ∧ ((True → False) ∧ (p4 ∨ p7))) → (((p3 ∨ p3) → False) → ((p1 → p7) ∧ (p0 → p6)))) ∧ ((((p4 → p6) → False) → ((p6 ∧ p0) → (p5 ∨ False))) → (((p0 ∧ False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_37 : (((p4 → p6) → False) → ((p6 ∧ p0) → (p5 ∨ False))) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        have assump_38 : (p4 → p6) := by
          intro assump_20
          exact assump_11
        let assump_19 := assump_9 assump_38
        apply False.elim assump_19
    let assump_8 := assump_3 assump_37
    have assump_39 : ((p0 ∧ False) → False) := by
      intro assump_27
      cases assump_27
      case intro assump_28 assump_29 =>
        apply False.elim assump_29
    let assump_26 := assump_8 assump_39
    apply False.elim assump_26


variable (p1 p2 p6 p0 p3 p4 : Prop)
theorem file52_16442 : (((((False → p6) ∨ (p0 ∧ False)) ∨ ((p0 → False) → False)) → False) → ((((True ∨ p6) ∧ (False → False)) ∧ ((p6 ∨ False) ∨ (p2 ∧ p1))) → (((p4 ∧ p6) → (False ∨ p4)) → ((p1 ∨ False) ∨ (p3 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_7
        case inl assump_16 =>
          cases assump_16
          case inl assump_18 =>
            apply Or.inr
            intro assump_24
            have assump_78 : (((False → p6) ∨ (p0 ∧ False)) ∨ ((p0 → False) → False)) := by
              apply Or.inl
              apply Or.inl
              intro assump_29
              apply False.elim assump_29
            let assump_28 := assump_1 assump_78
            apply False.elim assump_28
          case inr assump_19 =>
            apply False.elim assump_19
        case inr assump_17 =>
          cases assump_17
          case intro assump_37 assump_38 =>
            apply Or.inl
            apply Or.inl
            exact assump_38
      case inr assump_11 =>
        cases assump_7
        case inl assump_49 =>
          cases assump_49
          case inl assump_51 =>
            apply Or.inr
            intro assump_57
            have assump_79 : (((False → p6) ∨ (p0 ∧ False)) ∨ ((p0 → False) → False)) := by
              apply Or.inl
              apply Or.inl
              intro assump_62
              apply False.elim assump_62
            let assump_61 := assump_1 assump_79
            apply False.elim assump_61
          case inr assump_52 =>
            apply False.elim assump_52
        case inr assump_50 =>
          cases assump_50
          case intro assump_70 assump_71 =>
            apply Or.inl
            apply Or.inl
            exact assump_71


variable (p0 p7 p2 : Prop)
theorem file52_18366 : (((((p0 → False) → (p2 ∨ p7)) → ((p2 ∧ False) → (p2 → p7))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p0 → False) → (p2 ∨ p7)) → ((p2 ∧ False) → (p2 → p7))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p3 p2 p7 p4 p1 : Prop)
theorem file52_18822 : ((((((p7 → False) ∧ (False ∨ True)) → ((p1 ∨ False) ∨ (p2 ∧ True))) ∨ (((p5 ∨ p7) ∨ (True ∧ p7)) ∧ ((p7 ∧ p2) → False))) ∧ ((((True ∨ p1) → False) → ((p3 ∨ False) ∧ (p2 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_118 : (((True ∨ p1) → False) → ((p3 ∨ False) ∧ (p2 → p4))) := by
        intro assump_11
        apply And.intro
        have assump_119 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_14 := assump_11 assump_119
        apply False.elim assump_14
        intro assump_18
        have assump_120 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_23 := assump_11 assump_120
        apply False.elim assump_23
      let assump_10 := assump_3 assump_118
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_30 assump_31 =>
        cases assump_30
        case inl assump_32 =>
          cases assump_32
          case inl assump_34 =>
            have assump_121 : (((True ∨ p1) → False) → ((p3 ∨ False) ∧ (p2 → p4))) := by
              intro assump_43
              apply And.intro
              have assump_122 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_46 := assump_43 assump_122
              apply False.elim assump_46
              intro assump_50
              have assump_123 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_55 := assump_43 assump_123
              apply False.elim assump_55
            let assump_42 := assump_3 assump_121
            apply False.elim assump_42
          case inr assump_35 =>
            have assump_124 : (((True ∨ p1) → False) → ((p3 ∨ False) ∧ (p2 → p4))) := by
              intro assump_69
              apply And.intro
              have assump_125 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_72 := assump_69 assump_125
              apply False.elim assump_72
              intro assump_76
              have assump_126 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_81 := assump_69 assump_126
              apply False.elim assump_81
            let assump_68 := assump_3 assump_124
            apply False.elim assump_68
        case inr assump_33 =>
          cases assump_33
          case intro assump_88 assump_89 =>
            have assump_127 : (((True ∨ p1) → False) → ((p3 ∨ False) ∧ (p2 → p4))) := by
              intro assump_99
              apply And.intro
              have assump_128 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_102 := assump_99 assump_128
              apply False.elim assump_102
              intro assump_106
              have assump_129 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_111 := assump_99 assump_129
              apply False.elim assump_111
            let assump_98 := assump_3 assump_127
            apply False.elim assump_98


variable (p0 p6 p2 p7 : Prop)
theorem file52_22137 : ((((((p0 → False) → False) → ((p0 → False) ∨ (False ∧ p6))) → (((True ∧ True) ∨ (p7 ∧ p7)) → False)) ∧ ((((p7 ∧ False) ∧ (p7 ∨ p2)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p7 ∧ False) ∧ (p7 ∨ p2)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p6 p2 p3 p7 p5 p1 p0 p4 : Prop)
theorem file52_22755 : (((((True ∨ p0) ∨ (False ∨ False)) ∨ ((p7 ∨ p0) ∧ (False ∨ True))) ∨ (((p1 ∨ p2) ∧ (True → False)) → ((p4 ∨ p3) → (p7 → p3)))) ∧ ((((p2 → True) → (p3 → p6)) ∨ ((p5 ∨ True) ∧ (p3 ∧ p5))) → (((False → False) → False) → False))) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    have assump_58 : (False → False) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_2 assump_58
    apply False.elim assump_12
  case inr assump_6 =>
    cases assump_6
    case intro assump_19 assump_20 =>
      cases assump_19
      case inl assump_21 =>
        cases assump_20
        case intro assump_25 assump_26 =>
          have assump_59 : (False → False) := by
            intro assump_35
            apply False.elim assump_35
          let assump_34 := assump_2 assump_59
          apply False.elim assump_34
      case inr assump_22 =>
        cases assump_20
        case intro assump_43 assump_44 =>
          have assump_60 : (False → False) := by
            intro assump_52
            apply False.elim assump_52
          let assump_51 := assump_2 assump_60
          apply False.elim assump_51


variable (p6 p5 p0 p3 p7 : Prop)
theorem file52_24072 : ((((((p7 ∧ p7) → (p3 ∨ True)) → False) ∨ (((p6 ∧ True) → False) ∧ ((False ∨ False) → False))) ∧ ((((p0 ∧ p0) → (False ∧ p7)) ∨ ((p0 → False) → False)) ∧ (((p5 → False) → False) ∧ ((p3 → p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            have assump_82 : (p3 → p3) := by
              intro assump_21
              exact assump_21
            let assump_20 := assump_15 assump_82
            apply False.elim assump_20
        case inr assump_11 =>
          cases assump_9
          case intro assump_29 assump_30 =>
            have assump_83 : (p3 → p3) := by
              intro assump_36
              exact assump_36
            let assump_35 := assump_30 assump_83
            apply False.elim assump_35
    case inr assump_5 =>
      cases assump_5
      case intro assump_42 assump_43 =>
        cases assump_3
        case intro assump_48 assump_49 =>
          cases assump_48
          case inl assump_50 =>
            cases assump_49
            case intro assump_54 assump_55 =>
              have assump_84 : (p3 → p3) := by
                intro assump_61
                exact assump_61
              let assump_60 := assump_55 assump_84
              apply False.elim assump_60
          case inr assump_51 =>
            cases assump_49
            case intro assump_69 assump_70 =>
              have assump_85 : (p3 → p3) := by
                intro assump_76
                exact assump_76
              let assump_75 := assump_70 assump_85
              apply False.elim assump_75


variable (p7 p1 p0 p2 p3 : Prop)
theorem file52_25919 : (((((True → p3) ∨ (p2 → True)) → ((p1 ∧ p0) ∧ (p7 ∨ p7))) ∧ (((p1 ∧ False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p1 ∧ False) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p6 p5 p1 p0 p7 : Prop)
theorem file52_26389 : ((((((p6 ∨ True) → (True → p7)) → False) ∧ (((p6 → p5) ∧ (False → p7)) ∨ ((p6 ∨ p1) ∧ (p5 → p0)))) ∧ ((((p6 ∧ p1) ∨ (False → p7)) → ((False ∧ p5) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_64 : (((p6 ∧ p1) ∨ (False → p7)) → ((False ∧ p5) → False)) := by
            intro assump_19
            intro assump_20
            cases assump_20
            case intro assump_21 assump_22 =>
              apply False.elim assump_21
          let assump_18 := assump_3 assump_64
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case intro assump_28 assump_29 =>
          cases assump_28
          case inl assump_30 =>
            have assump_65 : (((p6 ∧ p1) ∨ (False → p7)) → ((False ∧ p5) → False)) := by
              intro assump_39
              intro assump_40
              cases assump_40
              case intro assump_41 assump_42 =>
                apply False.elim assump_41
            let assump_38 := assump_3 assump_65
            apply False.elim assump_38
          case inr assump_31 =>
            have assump_66 : (((p6 ∧ p1) ∨ (False → p7)) → ((False ∧ p5) → False)) := by
              intro assump_55
              intro assump_56
              cases assump_56
              case intro assump_57 assump_58 =>
                apply False.elim assump_57
            let assump_54 := assump_3 assump_66
            apply False.elim assump_54


variable (p0 p7 : Prop)
theorem file52_28091 : (((((True → False) → False) ∨ ((p0 → p7) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : (((True → False) → False) ∨ ((p0 → p7) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p5 p3 p2 p1 p4 : Prop)
theorem file52_28542 : (((((p0 ∨ p0) ∧ (p3 ∧ p3)) → ((p0 ∨ p4) ∧ (True ∨ p2))) ∧ (((p3 → False) → False) → ((False ∨ p4) → (True ∨ p2)))) ∨ ((((p5 ∨ p2) ∨ (p1 → False)) → False) → (((p1 ∧ p5) → False) ∧ ((True ∨ p3) ∨ (p4 → False))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply Or.inl
        exact assump_4
    case inr assump_5 =>
      cases assump_3
      case intro assump_16 assump_17 =>
        apply Or.inl
        exact assump_5
  cases assump_1
  case intro assump_22 assump_23 =>
    cases assump_22
    case inl assump_24 =>
      cases assump_23
      case intro assump_28 assump_29 =>
        apply Or.inl
        apply True.intro
    case inr assump_25 =>
      cases assump_23
      case intro assump_36 assump_37 =>
        apply Or.inl
        apply True.intro
  intro assump_42
  intro assump_43
  cases assump_43
  case inl assump_44 =>
    apply False.elim assump_44
  case inr assump_45 =>
    apply Or.inl
    apply True.intro


variable (p5 p6 p1 p2 p3 p0 : Prop)
theorem file52_29728 : ((((((p1 ∧ p0) ∧ (p0 → p6)) ∨ ((p3 ∨ p2) → False)) → (((p0 ∨ p1) ∨ (p1 → p5)) ∨ ((p0 ∨ True) → False))) → False) → False) := by
  intro assump_1
  have assump_47 : ((((p1 ∧ p0) ∧ (p0 → p6)) ∨ ((p3 ∨ p2) → False)) → (((p0 ∨ p1) ∨ (p1 → p5)) ∨ ((p0 ∨ True) → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_11
    case inr assump_7 =>
      apply Or.inl
      apply Or.inr
      intro assump_20
      have assump_48 : ((((p1 ∧ p0) ∧ (p0 → p6)) ∨ ((p3 ∨ p2) → False)) → (((p0 ∨ p1) ∨ (p1 → p5)) ∨ ((p0 ∨ True) → False))) := by
        intro assump_26
        cases assump_26
        case inl assump_27 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            cases assump_29
            case intro assump_31 assump_32 =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_32
        case inr assump_28 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          exact assump_20
      let assump_25 := assump_1 assump_48
      apply False.elim assump_25
  let assump_4 := assump_1 assump_47
  apply False.elim assump_4


variable (p5 p7 p2 p4 p1 p0 p3 : Prop)
theorem file52_31159 : (((((False → p1) ∧ (p4 ∧ p5)) ∨ ((p4 → p7) ∨ (p3 → p2))) ∧ (((True ∧ p1) → False) ∧ ((True ∨ p0) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            have assump_52 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_22 := assump_17 assump_52
            apply False.elim assump_22
    case inr assump_5 =>
      cases assump_5
      case inl assump_26 =>
        cases assump_3
        case intro assump_30 assump_31 =>
          have assump_53 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_36 := assump_31 assump_53
          apply False.elim assump_36
      case inr assump_27 =>
        cases assump_3
        case intro assump_42 assump_43 =>
          have assump_54 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_48 := assump_43 assump_54
          apply False.elim assump_48


variable (p6 p0 p4 p2 p1 p5 p7 : Prop)
theorem file52_32441 : (((((True ∨ False) → False) ∧ ((p6 → p5) ∧ (False ∨ p0))) → (((p2 → False) ∧ (p2 → p7)) → False)) → ((((True ∨ True) ∧ (p1 ∧ False)) ∧ ((p5 ∨ p6) ∨ (p4 → p0))) → False)) := by
  intro assump_1
  intro assump_2
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


variable (p5 p1 p2 p4 p7 p0 : Prop)
theorem file52_33096 : (((((p4 ∨ p7) → False) → ((p5 ∨ p1) ∨ (False ∧ p7))) → (((True ∧ p1) ∨ (p4 ∨ p0)) ∧ ((p1 → False) → False))) → ((((p7 ∧ p2) → False) ∨ ((p2 → p2) → False)) → (((p4 ∨ True) ∨ (False ∧ True)) ∨ ((p4 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_4 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p1 p0 p6 p2 p3 : Prop)
theorem file52_33618 : ((((((p0 ∧ True) → (p6 → False)) → False) ∧ (((p0 → False) ∧ (p1 ∧ p1)) ∨ ((p2 → False) ∨ (p3 → False)))) ∧ ((((p1 ∨ p0) ∨ (p0 → False)) ∨ ((p1 ∧ False) ∨ (False ∧ p2))) → False)) → False) := by
  intro assump_52
  cases assump_52
  case intro assump_53 assump_54 =>
    cases assump_53
    case intro assump_55 assump_56 =>
      cases assump_56
      case inl assump_59 =>
        cases assump_59
        case intro assump_61 assump_62 =>
          cases assump_62
          case intro assump_65 assump_66 =>
            have assump_111 : (((p1 ∨ p0) ∨ (p0 → False)) ∨ ((p1 ∧ False) ∨ (False ∧ p2))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_66
            let assump_73 := assump_54 assump_111
            apply False.elim assump_73
      case inr assump_60 =>
        cases assump_60
        case inl assump_77 =>
          have assump_112 : (((p1 ∨ p0) ∨ (p0 → False)) ∨ ((p1 ∧ False) ∨ (False ∧ p2))) := by
            apply Or.inl
            apply Or.inr
            intro assump_84
            have assump_113 : (((p1 ∨ p0) ∨ (p0 → False)) ∨ ((p1 ∧ False) ∨ (False ∧ p2))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_84
            let assump_88 := assump_54 assump_113
            apply False.elim assump_88
          let assump_83 := assump_54 assump_112
          apply False.elim assump_83
        case inr assump_78 =>
          have assump_114 : (((p1 ∨ p0) ∨ (p0 → False)) ∨ ((p1 ∧ False) ∨ (False ∧ p2))) := by
            apply Or.inl
            apply Or.inr
            intro assump_100
            have assump_115 : (((p1 ∨ p0) ∨ (p0 → False)) ∨ ((p1 ∧ False) ∨ (False ∧ p2))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_100
            let assump_104 := assump_54 assump_115
            apply False.elim assump_104
          let assump_99 := assump_54 assump_114
          apply False.elim assump_99


variable (p1 p7 p3 p6 : Prop)
theorem file52_35706 : (((((p1 ∧ True) ∧ (p3 → True)) → False) → False) → ((((True ∧ p1) → False) ∨ ((p1 ∨ p7) → False)) → (((True ∨ True) → (False → False)) ∨ ((p6 → False) ∨ (p6 ∧ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  case inr assump_4 =>
    apply Or.inl
    intro assump_17
    intro assump_18
    apply False.elim assump_18


variable (p4 p2 p7 p6 : Prop)
theorem file52_36208 : ((((((True ∨ p7) → False) ∧ ((False ∨ p2) ∧ (p6 → False))) → False) → ((((p2 → p4) → False) → ((p4 → False) ∧ (False → False))) → False)) → False) := by
  intro assump_1
  have assump_46 : ((((True ∨ p7) → False) ∧ ((False ∨ p2) ∧ (p6 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          have assump_47 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_22 := assump_6 assump_47
          apply False.elim assump_22
  let assump_4 := assump_1 assump_46
  have assump_48 : (((p2 → p4) → False) → ((p4 → False) ∧ (False → False))) := by
    intro assump_27
    apply And.intro
    intro assump_28
    have assump_49 : (p2 → p4) := by
      intro assump_34
      exact assump_28
    let assump_33 := assump_27 assump_49
    apply False.elim assump_33
    intro assump_40
    apply False.elim assump_40
  let assump_26 := assump_4 assump_48
  apply False.elim assump_26


variable (p0 p4 p5 p3 p7 p2 : Prop)
theorem file52_37417 : ((((((p7 → p5) → False) ∨ ((p7 → p2) → (True ∨ p2))) → (((False ∧ p0) → (True → p3)) ∨ ((p2 → False) ∧ (p4 → True)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p7 → p5) → False) ∨ ((p7 → p2) → (True ∨ p2))) → (((False ∧ p0) → (True → p3)) ∨ ((p2 → False) ∧ (p4 → True)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    case inr assump_7 =>
      apply Or.inl
      intro assump_20
      intro assump_21
      cases assump_20
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p7 p5 p6 p3 p1 p4 p2 : Prop)
theorem file52_38253 : ((((((p4 ∨ p3) → False) ∧ ((False → p4) ∨ (p4 ∨ p5))) → (((p1 → False) → (p7 ∧ p7)) ∧ ((p1 → False) → False))) ∧ ((((p1 ∨ p3) → False) ∧ ((p3 ∧ p1) ∧ (p2 ∧ p5))) ∧ (((p6 ∨ True) ∨ (p3 → False)) ∨ ((p4 ∨ False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              cases assump_7
              case inl assump_26 =>
                cases assump_26
                case inl assump_28 =>
                  cases assump_28
                  case inl assump_30 =>
                    have assump_70 : (p1 ∨ p3) := by
                      apply Or.inl
                      exact assump_15
                    let assump_39 := assump_8 assump_70
                    apply False.elim assump_39
                  case inr assump_31 =>
                    have assump_71 : (p1 ∨ p3) := by
                      apply Or.inl
                      exact assump_15
                    let assump_49 := assump_8 assump_71
                    apply False.elim assump_49
                case inr assump_29 =>
                  have assump_72 : p3 := by
                    exact assump_14
                  let assump_55 := assump_29 assump_72
                  apply False.elim assump_55
              case inr assump_27 =>
                have assump_73 : (p1 ∨ p3) := by
                  apply Or.inl
                  exact assump_15
                let assump_66 := assump_8 assump_73
                apply False.elim assump_66


variable (p7 p3 p2 p5 p1 p6 : Prop)
theorem file52_40111 : (((((p6 ∧ False) ∧ (p2 ∧ p6)) ∧ ((p6 → False) → False)) ∧ (((True ∨ False) → (p7 ∨ p3)) → False)) → ((((p1 ∨ p5) ∨ (p3 ∧ False)) → ((p3 ∨ False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          apply False.elim assump_12


variable (p7 p4 p6 p3 : Prop)
theorem file52_40638 : (((((p3 ∧ p7) ∧ (True ∧ p6)) → False) ∧ (((p4 ∨ p3) → False) ∧ ((False → False) ∧ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_20 : True := by
          apply True.intro
        let assump_16 := assump_11 assump_20
        apply False.elim assump_16


variable (p5 p6 p0 p1 : Prop)
theorem file52_41134 : (((((p6 → True) → (p1 → p0)) → ((p6 → False) → (True ∨ p5))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p6 → True) → (p1 → p0)) → ((p6 → False) → (True ∨ p5))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p0 p1 p6 p3 p5 p4 p7 p2 : Prop)
theorem file52_41527 : (((((p0 → False) ∨ (p1 ∧ p2)) → ((p2 ∧ p5) → (p7 ∨ p3))) ∧ (((p6 → False) ∧ (False → False)) ∧ ((False ∧ p4) ∧ (p3 ∨ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_16


variable (p4 p0 p5 p1 p2 p7 p6 p3 : Prop)
theorem file52_42091 : (((((False ∧ p1) → False) ∨ ((p0 ∨ p0) → False)) → False) → ((((p6 → p6) ∨ (p1 → p4)) ∨ ((p4 ∧ p7) → False)) → (((False → p3) ∨ (False ∧ p5)) ∨ ((False ∧ p2) ∧ (p0 ∨ p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_11
      apply False.elim assump_11
    case inr assump_6 =>
      apply Or.inl
      apply Or.inl
      intro assump_18
      apply False.elim assump_18
  case inr assump_4 =>
    apply Or.inl
    apply Or.inl
    intro assump_25
    apply False.elim assump_25


variable (p3 p0 p4 p1 p7 p6 p5 : Prop)
theorem file52_42771 : ((((((p6 ∧ p4) → (p1 ∨ p4)) ∨ ((p4 → False) → False)) ∧ (((True → False) ∧ (p6 → False)) ∨ ((p6 → p5) ∨ (True → p0)))) ∧ ((((p6 → False) ∧ (p4 ∧ p5)) ∧ ((p3 → False) ∧ (p3 ∧ p7))) ∧ (((p3 ∧ True) ∧ (p3 ∨ p7)) ∧ ((p0 → p6) ∨ (False → p6))))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_17
      case inl assump_19 =>
        cases assump_18
        case inl assump_23 =>
          cases assump_23
          case intro assump_25 assump_26 =>
            cases assump_16
            case intro assump_31 assump_32 =>
              cases assump_31
              case intro assump_33 assump_34 =>
                cases assump_33
                case intro assump_35 assump_36 =>
                  cases assump_36
                  case intro assump_39 assump_40 =>
                    cases assump_34
                    case intro assump_45 assump_46 =>
                      cases assump_46
                      case intro assump_49 assump_50 =>
                        cases assump_32
                        case intro assump_55 assump_56 =>
                          cases assump_55
                          case intro assump_57 assump_58 =>
                            cases assump_57
                            case intro assump_59 assump_60 =>
                              cases assump_58
                              case inl assump_65 =>
                                cases assump_56
                                case inl assump_69 =>
                                  have assump_581 : p3 := by
                                    exact assump_65
                                  let assump_78 := assump_45 assump_581
                                  apply False.elim assump_78
                                case inr assump_70 =>
                                  have assump_582 : p3 := by
                                    exact assump_65
                                  let assump_89 := assump_45 assump_582
                                  apply False.elim assump_89
                              case inr assump_66 =>
                                cases assump_56
                                case inl assump_95 =>
                                  have assump_583 : p3 := by
                                    exact assump_59
                                  let assump_104 := assump_45 assump_583
                                  apply False.elim assump_104
                                case inr assump_96 =>
                                  have assump_584 : p3 := by
                                    exact assump_59
                                  let assump_115 := assump_45 assump_584
                                  apply False.elim assump_115
        case inr assump_24 =>
          cases assump_24
          case inl assump_119 =>
            cases assump_16
            case intro assump_123 assump_124 =>
              cases assump_123
              case intro assump_125 assump_126 =>
                cases assump_125
                case intro assump_127 assump_128 =>
                  cases assump_128
                  case intro assump_131 assump_132 =>
                    cases assump_126
                    case intro assump_137 assump_138 =>
                      cases assump_138
                      case intro assump_141 assump_142 =>
                        cases assump_124
                        case intro assump_147 assump_148 =>
                          cases assump_147
                          case intro assump_149 assump_150 =>
                            cases assump_149
                            case intro assump_151 assump_152 =>
                              cases assump_150
                              case inl assump_157 =>
                                cases assump_148
                                case inl assump_161 =>
                                  have assump_585 : p3 := by
                                    exact assump_157
                                  let assump_170 := assump_137 assump_585
                                  apply False.elim assump_170
                                case inr assump_162 =>
                                  have assump_586 : p3 := by
                                    exact assump_157
                                  let assump_181 := assump_137 assump_586
                                  apply False.elim assump_181
                              case inr assump_158 =>
                                cases assump_148
                                case inl assump_187 =>
                                  have assump_587 : p3 := by
                                    exact assump_151
                                  let assump_196 := assump_137 assump_587
                                  apply False.elim assump_196
                                case inr assump_188 =>
                                  have assump_588 : p3 := by
                                    exact assump_151
                                  let assump_207 := assump_137 assump_588
                                  apply False.elim assump_207
          case inr assump_120 =>
            cases assump_16
            case intro assump_213 assump_214 =>
              cases assump_213
              case intro assump_215 assump_216 =>
                cases assump_215
                case intro assump_217 assump_218 =>
                  cases assump_218
                  case intro assump_221 assump_222 =>
                    cases assump_216
                    case intro assump_227 assump_228 =>
                      cases assump_228
                      case intro assump_231 assump_232 =>
                        cases assump_214
                        case intro assump_237 assump_238 =>
                          cases assump_237
                          case intro assump_239 assump_240 =>
                            cases assump_239
                            case intro assump_241 assump_242 =>
                              cases assump_240
                              case inl assump_247 =>
                                cases assump_238
                                case inl assump_251 =>
                                  have assump_589 : p3 := by
                                    exact assump_247
                                  let assump_260 := assump_227 assump_589
                                  apply False.elim assump_260
                                case inr assump_252 =>
                                  have assump_590 : p3 := by
                                    exact assump_247
                                  let assump_271 := assump_227 assump_590
                                  apply False.elim assump_271
                              case inr assump_248 =>
                                cases assump_238
                                case inl assump_277 =>
                                  have assump_591 : p3 := by
                                    exact assump_241
                                  let assump_286 := assump_227 assump_591
                                  apply False.elim assump_286
                                case inr assump_278 =>
                                  have assump_592 : p3 := by
                                    exact assump_241
                                  let assump_297 := assump_227 assump_592
                                  apply False.elim assump_297
      case inr assump_20 =>
        cases assump_18
        case inl assump_303 =>
          cases assump_303
          case intro assump_305 assump_306 =>
            cases assump_16
            case intro assump_311 assump_312 =>
              cases assump_311
              case intro assump_313 assump_314 =>
                cases assump_313
                case intro assump_315 assump_316 =>
                  cases assump_316
                  case intro assump_319 assump_320 =>
                    cases assump_314
                    case intro assump_325 assump_326 =>
                      cases assump_326
                      case intro assump_329 assump_330 =>
                        cases assump_312
                        case intro assump_335 assump_336 =>
                          cases assump_335
                          case intro assump_337 assump_338 =>
                            cases assump_337
                            case intro assump_339 assump_340 =>
                              cases assump_338
                              case inl assump_345 =>
                                cases assump_336
                                case inl assump_349 =>
                                  have assump_593 : p3 := by
                                    exact assump_345
                                  let assump_358 := assump_325 assump_593
                                  apply False.elim assump_358
                                case inr assump_350 =>
                                  have assump_594 : p3 := by
                                    exact assump_345
                                  let assump_369 := assump_325 assump_594
                                  apply False.elim assump_369
                              case inr assump_346 =>
                                cases assump_336
                                case inl assump_375 =>
                                  have assump_595 : p3 := by
                                    exact assump_339
                                  let assump_384 := assump_325 assump_595
                                  apply False.elim assump_384
                                case inr assump_376 =>
                                  have assump_596 : p3 := by
                                    exact assump_339
                                  let assump_395 := assump_325 assump_596
                                  apply False.elim assump_395
        case inr assump_304 =>
          cases assump_304
          case inl assump_399 =>
            cases assump_16
            case intro assump_403 assump_404 =>
              cases assump_403
              case intro assump_405 assump_406 =>
                cases assump_405
                case intro assump_407 assump_408 =>
                  cases assump_408
                  case intro assump_411 assump_412 =>
                    cases assump_406
                    case intro assump_417 assump_418 =>
                      cases assump_418
                      case intro assump_421 assump_422 =>
                        cases assump_404
                        case intro assump_427 assump_428 =>
                          cases assump_427
                          case intro assump_429 assump_430 =>
                            cases assump_429
                            case intro assump_431 assump_432 =>
                              cases assump_430
                              case inl assump_437 =>
                                cases assump_428
                                case inl assump_441 =>
                                  have assump_597 : p3 := by
                                    exact assump_437
                                  let assump_450 := assump_417 assump_597
                                  apply False.elim assump_450
                                case inr assump_442 =>
                                  have assump_598 : p3 := by
                                    exact assump_437
                                  let assump_461 := assump_417 assump_598
                                  apply False.elim assump_461
                              case inr assump_438 =>
                                cases assump_428
                                case inl assump_467 =>
                                  have assump_599 : p3 := by
                                    exact assump_431
                                  let assump_476 := assump_417 assump_599
                                  apply False.elim assump_476
                                case inr assump_468 =>
                                  have assump_600 : p3 := by
                                    exact assump_431
                                  let assump_487 := assump_417 assump_600
                                  apply False.elim assump_487
          case inr assump_400 =>
            cases assump_16
            case intro assump_493 assump_494 =>
              cases assump_493
              case intro assump_495 assump_496 =>
                cases assump_495
                case intro assump_497 assump_498 =>
                  cases assump_498
                  case intro assump_501 assump_502 =>
                    cases assump_496
                    case intro assump_507 assump_508 =>
                      cases assump_508
                      case intro assump_511 assump_512 =>
                        cases assump_494
                        case intro assump_517 assump_518 =>
                          cases assump_517
                          case intro assump_519 assump_520 =>
                            cases assump_519
                            case intro assump_521 assump_522 =>
                              cases assump_520
                              case inl assump_527 =>
                                cases assump_518
                                case inl assump_531 =>
                                  have assump_601 : p3 := by
                                    exact assump_527
                                  let assump_540 := assump_507 assump_601
                                  apply False.elim assump_540
                                case inr assump_532 =>
                                  have assump_602 : p3 := by
                                    exact assump_527
                                  let assump_551 := assump_507 assump_602
                                  apply False.elim assump_551
                              case inr assump_528 =>
                                cases assump_518
                                case inl assump_557 =>
                                  have assump_603 : p3 := by
                                    exact assump_521
                                  let assump_566 := assump_507 assump_603
                                  apply False.elim assump_566
                                case inr assump_558 =>
                                  have assump_604 : p3 := by
                                    exact assump_521
                                  let assump_577 := assump_507 assump_604
                                  apply False.elim assump_577


variable (p7 p5 p4 p3 p6 p1 p0 p2 : Prop)
theorem file52_57594 : (((((p3 ∨ p2) ∨ (p5 → False)) ∨ ((p1 → False) → False)) ∨ (((p5 ∧ p5) ∨ (p5 → False)) → False)) → ((((p3 ∧ p0) ∨ (p2 → p2)) ∨ ((p0 ∨ p4) → (False → False))) ∨ (((p6 ∨ p3) ∧ (p7 → p4)) → ((p6 ∨ True) → (True → True))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          intro assump_12
          exact assump_12
        case inr assump_9 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          intro assump_17
          exact assump_17
      case inr assump_7 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        intro assump_22
        exact assump_22
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      intro assump_27
      exact assump_27
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_32
    exact assump_32


variable (p5 p4 p2 p3 p0 p1 : Prop)
theorem file52_58729 : ((((((p0 ∧ p2) ∧ (p5 ∨ p1)) ∧ ((p1 → p3) ∨ (True → p2))) → False) ∧ ((((p3 ∧ False) ∧ (p4 → False)) → ((p0 ∨ p0) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p3 ∧ False) ∧ (p4 → False)) → ((p0 ∨ p0) ∨ (False → False))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p2 p6 p3 p0 p4 p1 : Prop)
theorem file52_59360 : (((((p2 → False) ∧ (p1 → False)) ∧ ((p4 → True) ∨ (p0 ∨ p6))) ∧ (((False → False) → False) ∧ ((p0 ∨ p3) ∨ (False → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case inl assump_12 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case inl assump_20 =>
              cases assump_20
              case inl assump_22 =>
                have assump_136 : (False → False) := by
                  intro assump_28
                  apply False.elim assump_28
                let assump_27 := assump_16 assump_136
                apply False.elim assump_27
              case inr assump_23 =>
                have assump_137 : (False → False) := by
                  intro assump_38
                  apply False.elim assump_38
                let assump_37 := assump_16 assump_137
                apply False.elim assump_37
            case inr assump_21 =>
              have assump_138 : (False → False) := by
                intro assump_48
                apply False.elim assump_48
              let assump_47 := assump_16 assump_138
              apply False.elim assump_47
        case inr assump_13 =>
          cases assump_13
          case inl assump_54 =>
            cases assump_3
            case intro assump_58 assump_59 =>
              cases assump_59
              case inl assump_62 =>
                cases assump_62
                case inl assump_64 =>
                  have assump_139 : (False → False) := by
                    intro assump_70
                    apply False.elim assump_70
                  let assump_69 := assump_58 assump_139
                  apply False.elim assump_69
                case inr assump_65 =>
                  have assump_140 : (False → False) := by
                    intro assump_80
                    apply False.elim assump_80
                  let assump_79 := assump_58 assump_140
                  apply False.elim assump_79
              case inr assump_63 =>
                have assump_141 : (False → False) := by
                  intro assump_90
                  apply False.elim assump_90
                let assump_89 := assump_58 assump_141
                apply False.elim assump_89
          case inr assump_55 =>
            cases assump_3
            case intro assump_98 assump_99 =>
              cases assump_99
              case inl assump_102 =>
                cases assump_102
                case inl assump_104 =>
                  have assump_142 : (False → False) := by
                    intro assump_110
                    apply False.elim assump_110
                  let assump_109 := assump_98 assump_142
                  apply False.elim assump_109
                case inr assump_105 =>
                  have assump_143 : (False → False) := by
                    intro assump_120
                    apply False.elim assump_120
                  let assump_119 := assump_98 assump_143
                  apply False.elim assump_119
              case inr assump_103 =>
                have assump_144 : (False → False) := by
                  intro assump_130
                  apply False.elim assump_130
                let assump_129 := assump_98 assump_144
                apply False.elim assump_129


variable (p0 p4 p6 p7 p2 p1 p5 p3 : Prop)
theorem file52_62889 : ((((((p7 → False) ∨ (True → p5)) ∨ ((p5 ∨ p3) ∧ (p3 → p2))) ∨ (((p3 ∧ p5) → False) → ((p0 ∨ p1) → (p4 → p1)))) ∧ ((((True ∨ False) ∨ (p1 ∨ p6)) ∨ ((p0 → p4) → (p1 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_58 : (((True ∨ False) ∨ (p1 ∨ p6)) ∨ ((p0 → p4) → (p1 ∧ p2))) := by
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_14 := assump_3 assump_58
          apply False.elim assump_14
        case inr assump_9 =>
          have assump_59 : (((True ∨ False) ∨ (p1 ∨ p6)) ∨ ((p0 → p4) → (p1 ∧ p2))) := by
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_22 := assump_3 assump_59
          apply False.elim assump_22
      case inr assump_7 =>
        cases assump_7
        case intro assump_26 assump_27 =>
          cases assump_26
          case inl assump_28 =>
            have assump_60 : (((True ∨ False) ∨ (p1 ∨ p6)) ∨ ((p0 → p4) → (p1 ∧ p2))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_36 := assump_3 assump_60
            apply False.elim assump_36
          case inr assump_29 =>
            have assump_61 : (((True ∨ False) ∨ (p1 ∨ p6)) ∨ ((p0 → p4) → (p1 ∧ p2))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_46 := assump_3 assump_61
            apply False.elim assump_46
    case inr assump_5 =>
      have assump_62 : (((True ∨ False) ∨ (p1 ∨ p6)) ∨ ((p0 → p4) → (p1 ∧ p2))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_54 := assump_3 assump_62
      apply False.elim assump_54


variable (p3 p0 p2 p6 p4 p7 p5 : Prop)
theorem file52_64981 : ((((((p7 ∨ p2) ∨ (p3 → False)) ∧ ((p4 ∨ p3) ∧ (True → False))) ∧ (((p0 → p3) ∨ (p4 ∧ p3)) → False)) ∧ ((((True ∧ p4) ∧ (p4 ∧ p5)) ∨ ((False ∧ p6) → False)) → False)) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_19
        case inl assump_21 =>
          cases assump_21
          case inl assump_23 =>
            cases assump_20
            case intro assump_27 assump_28 =>
              cases assump_27
              case inl assump_29 =>
                have assump_145 : (((True ∧ p4) ∧ (p4 ∧ p5)) ∨ ((False ∧ p6) → False)) := by
                  apply Or.inr
                  intro assump_40
                  cases assump_40
                  case intro assump_41 assump_42 =>
                    apply False.elim assump_41
                let assump_39 := assump_16 assump_145
                apply False.elim assump_39
              case inr assump_30 =>
                have assump_146 : (((True ∧ p4) ∧ (p4 ∧ p5)) ∨ ((False ∧ p6) → False)) := by
                  apply Or.inr
                  intro assump_57
                  cases assump_57
                  case intro assump_58 assump_59 =>
                    apply False.elim assump_58
                let assump_56 := assump_16 assump_146
                apply False.elim assump_56
          case inr assump_24 =>
            cases assump_20
            case intro assump_67 assump_68 =>
              cases assump_67
              case inl assump_69 =>
                have assump_147 : (((True ∧ p4) ∧ (p4 ∧ p5)) ∨ ((False ∧ p6) → False)) := by
                  apply Or.inr
                  intro assump_80
                  cases assump_80
                  case intro assump_81 assump_82 =>
                    apply False.elim assump_81
                let assump_79 := assump_16 assump_147
                apply False.elim assump_79
              case inr assump_70 =>
                have assump_148 : (((True ∧ p4) ∧ (p4 ∧ p5)) ∨ ((False ∧ p6) → False)) := by
                  apply Or.inr
                  intro assump_97
                  cases assump_97
                  case intro assump_98 assump_99 =>
                    apply False.elim assump_98
                let assump_96 := assump_16 assump_148
                apply False.elim assump_96
        case inr assump_22 =>
          cases assump_20
          case intro assump_107 assump_108 =>
            cases assump_107
            case inl assump_109 =>
              have assump_149 : (((True ∧ p4) ∧ (p4 ∧ p5)) ∨ ((False ∧ p6) → False)) := by
                apply Or.inr
                intro assump_120
                cases assump_120
                case intro assump_121 assump_122 =>
                  apply False.elim assump_121
              let assump_119 := assump_16 assump_149
              apply False.elim assump_119
            case inr assump_110 =>
              have assump_150 : (((True ∧ p4) ∧ (p4 ∧ p5)) ∨ ((False ∧ p6) → False)) := by
                apply Or.inr
                intro assump_137
                cases assump_137
                case intro assump_138 assump_139 =>
                  apply False.elim assump_138
              let assump_136 := assump_16 assump_150
              apply False.elim assump_136


variable (p2 p1 p0 p6 p3 p5 p4 : Prop)
theorem file52_68424 : ((((((p1 ∨ p3) ∨ (p5 ∨ False)) ∧ ((p2 ∧ False) ∧ (p0 ∨ p4))) → (((p4 ∨ p6) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_52 : ((((p1 ∨ p3) ∨ (p5 ∨ False)) ∧ ((p2 ∧ False) ∧ (p0 ∨ p4))) → (((p4 ∨ p6) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_10
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              apply False.elim assump_20
        case inr assump_14 =>
          cases assump_10
          case intro assump_27 assump_28 =>
            cases assump_27
            case intro assump_29 assump_30 =>
              apply False.elim assump_30
      case inr assump_12 =>
        cases assump_12
        case inl assump_35 =>
          cases assump_10
          case intro assump_39 assump_40 =>
            cases assump_39
            case intro assump_41 assump_42 =>
              apply False.elim assump_42
        case inr assump_36 =>
          apply False.elim assump_36
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4


variable (p1 p3 p4 p7 p2 p5 p6 : Prop)
theorem file52_69735 : (((((p3 → False) ∨ (p2 → False)) ∨ ((p4 → p7) ∧ (True → p6))) → (((False ∧ p5) → False) → False)) → ((((p1 ∨ p3) ∧ (p3 ∧ False)) ∧ ((p7 → False) → False)) → (((p7 → False) ∨ (p2 ∨ p4)) ∨ ((p6 → True) ∧ (p2 ∧ p7))))) := by
  intro assump_1
  intro assump_2
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


variable (p6 p5 p1 : Prop)
theorem file52_70427 : ((((((p6 ∨ p5) → (True ∨ p1)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p6 ∨ p5) → (True ∨ p1)) → False) → False) := by
    intro assump_5
    have assump_23 : ((p6 ∨ p5) → (True ∨ p1)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        apply True.intro
      case inr assump_11 =>
        apply Or.inl
        apply True.intro
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p7 p1 p2 p4 p0 : Prop)
theorem file52_71043 : (((((p0 ∨ p1) ∨ (p0 ∨ True)) → False) ∧ (((p6 ∨ False) ∧ (p7 ∨ p1)) ∨ ((p6 → p4) ∨ (False → p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            have assump_50 : ((p0 ∨ p1) ∨ (p0 ∨ True)) := by
              apply Or.inr
              apply Or.inr
              apply True.intro
            let assump_20 := assump_2 assump_50
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_51 : ((p0 ∨ p1) ∨ (p0 ∨ True)) := by
              apply Or.inl
              apply Or.inr
              exact assump_15
            let assump_28 := assump_2 assump_51
            apply False.elim assump_28
        case inr assump_11 =>
          apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case inl assump_34 =>
        have assump_52 : ((p0 ∨ p1) ∨ (p0 ∨ True)) := by
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_39 := assump_2 assump_52
        apply False.elim assump_39
      case inr assump_35 =>
        have assump_53 : ((p0 ∨ p1) ∨ (p0 ∨ True)) := by
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_46 := assump_2 assump_53
        apply False.elim assump_46


variable (p3 p2 p6 p5 p1 p0 p7 : Prop)
theorem file52_72585 : (((((p7 ∨ p3) ∧ (True ∧ p7)) → ((p2 ∨ p6) ∨ (p6 ∨ True))) → False) → ((((p2 → False) ∧ (p3 → p2)) → False) ∨ (((p1 → False) ∧ (p0 ∧ p1)) ∨ ((p6 ∨ p7) → (False ∨ p5))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_38 : (((p7 ∨ p3) ∧ (True ∧ p7)) → ((p2 ∨ p6) ∨ (p6 ∨ True))) := by
      intro assump_14
      cases assump_14
      case intro assump_15 assump_16 =>
        cases assump_15
        case inl assump_17 =>
          cases assump_16
          case intro assump_21 assump_22 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
        case inr assump_18 =>
          cases assump_16
          case intro assump_29 assump_30 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
    let assump_13 := assump_1 assump_38
    apply False.elim assump_13


variable (p7 p1 p6 p2 p0 p4 p5 : Prop)
theorem file52_73543 : (((((p6 ∧ p2) ∨ (False → False)) ∧ ((False → False) → False)) ∧ (((p0 ∨ p7) ∧ (p4 ∨ p5)) → False)) → ((((p5 ∧ p2) ∨ (p5 → p2)) → False) → (((p1 ∨ True) → (p2 → False)) → ((p6 → False) ∧ (p6 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_1
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          have assump_94 : (False → False) := by
            intro assump_29
            apply False.elim assump_29
          let assump_28 := assump_14 assump_94
          apply False.elim assump_28
      case inr assump_16 =>
        have assump_95 : (False → False) := by
          intro assump_43
          apply False.elim assump_43
        let assump_42 := assump_14 assump_95
        apply False.elim assump_42
  intro assump_49
  cases assump_1
  case intro assump_56 assump_57 =>
    cases assump_56
    case intro assump_58 assump_59 =>
      cases assump_58
      case inl assump_60 =>
        cases assump_60
        case intro assump_62 assump_63 =>
          have assump_96 : (False → False) := by
            intro assump_74
            apply False.elim assump_74
          let assump_73 := assump_59 assump_96
          apply False.elim assump_73
      case inr assump_61 =>
        have assump_97 : (False → False) := by
          intro assump_88
          apply False.elim assump_88
        let assump_87 := assump_59 assump_97
        apply False.elim assump_87


variable (p2 p1 p3 p7 p4 : Prop)
theorem file52_75203 : (((((p4 ∧ False) ∧ (p3 ∧ p7)) → False) ∧ (((p7 → p1) → (p2 → p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : ((p7 → p1) → (p2 → p2)) := by
      intro assump_9
      intro assump_10
      exact assump_10
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p5 p4 p1 p7 p2 p3 p6 : Prop)
theorem file52_75610 : ((((((False → p7) ∨ (p2 → p1)) ∨ ((p5 → False) → (p4 → False))) ∨ (((p3 ∧ False) → (p6 → False)) ∧ ((p7 → False) ∨ (p5 → p7)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → p7) ∨ (p2 → p1)) ∨ ((p5 → False) → (p4 → False))) ∨ (((p3 ∧ False) → (p6 → False)) ∧ ((p7 → False) ∨ (p5 → p7)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p4 p5 p7 p6 : Prop)
theorem file52_76152 : (((((True → False) → (p7 ∨ p3)) ∧ ((False ∧ p6) → False)) → False) → ((((p3 ∨ False) ∨ (True ∨ p4)) → False) ∧ (((p7 → p7) → (p3 ∧ p3)) ∨ ((p5 → False) ∧ (True ∧ True))))) := by
  intro assump_5
  apply And.intro
  intro assump_6
  cases assump_6
  case inl assump_7 =>
    cases assump_7
    case inl assump_9 =>
      have assump_112 : (((True → False) → (p7 ∨ p3)) ∧ ((False ∧ p6) → False)) := by
        apply And.intro
        intro assump_16
        apply Or.inr
        exact assump_9
        intro assump_19
        cases assump_19
        case intro assump_20 assump_21 =>
          apply False.elim assump_20
      let assump_15 := assump_5 assump_112
      apply False.elim assump_15
    case inr assump_10 =>
      apply False.elim assump_10
  case inr assump_8 =>
    cases assump_8
    case inl assump_29 =>
      have assump_113 : (((True → False) → (p7 ∨ p3)) ∧ ((False ∧ p6) → False)) := by
        apply And.intro
        intro assump_36
        have assump_114 : True := by
          apply True.intro
        let assump_39 := assump_36 assump_114
        apply False.elim assump_39
        intro assump_43
        cases assump_43
        case intro assump_44 assump_45 =>
          apply False.elim assump_44
      let assump_35 := assump_5 assump_113
      apply False.elim assump_35
    case inr assump_30 =>
      have assump_115 : (((True → False) → (p7 ∨ p3)) ∧ ((False ∧ p6) → False)) := by
        apply And.intro
        intro assump_56
        have assump_116 : True := by
          apply True.intro
        let assump_59 := assump_56 assump_116
        apply False.elim assump_59
        intro assump_63
        cases assump_63
        case intro assump_64 assump_65 =>
          apply False.elim assump_64
      let assump_55 := assump_5 assump_115
      apply False.elim assump_55
  apply Or.inl
  intro assump_73
  apply And.intro
  have assump_117 : (((True → False) → (p7 ∨ p3)) ∧ ((False ∧ p6) → False)) := by
    apply And.intro
    intro assump_78
    have assump_118 : True := by
      apply True.intro
    let assump_81 := assump_78 assump_118
    apply False.elim assump_81
    intro assump_85
    cases assump_85
    case intro assump_86 assump_87 =>
      apply False.elim assump_86
  let assump_77 := assump_5 assump_117
  apply False.elim assump_77
  have assump_119 : (((True → False) → (p7 ∨ p3)) ∧ ((False ∧ p6) → False)) := by
    apply And.intro
    intro assump_97
    have assump_120 : True := by
      apply True.intro
    let assump_100 := assump_97 assump_120
    apply False.elim assump_100
    intro assump_104
    cases assump_104
    case intro assump_105 assump_106 =>
      apply False.elim assump_105
  let assump_96 := assump_5 assump_119
  apply False.elim assump_96


variable (p1 p5 p7 p4 : Prop)
theorem file52_78936 : (((((p4 → False) → (False → False)) ∨ ((p1 ∨ p5) ∨ (p4 ∧ p7))) → False) → False) := by
  intro assump_5
  have assump_16 : (((p4 → False) → (False → False)) ∨ ((p1 ∨ p5) ∨ (p4 ∧ p7))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  let assump_8 := assump_5 assump_16
  apply False.elim assump_8


variable (p1 p5 p0 p6 p4 p2 p3 : Prop)
theorem file52_79341 : ((((((p0 → p3) ∨ (p3 → p3)) ∨ ((p6 ∧ p3) → False)) ∧ (((p2 → False) → (False → False)) ∧ ((p5 → False) ∨ (p4 → False)))) ∧ ((((p6 ∨ False) → False) → ((p3 ∨ False) ∨ (p6 → p4))) → (((p0 ∧ p1) → (p1 ∨ p6)) → False))) → False) := by
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
            cases assump_13
            case inl assump_16 =>
              have assump_196 : (((p6 ∨ False) → False) → ((p3 ∨ False) ∨ (p6 → p4))) := by
                intro assump_23
                apply Or.inr
                intro assump_26
                have assump_197 : (p6 ∨ False) := by
                  apply Or.inl
                  exact assump_26
                let assump_30 := assump_23 assump_197
                apply False.elim assump_30
              let assump_22 := assump_3 assump_196
              have assump_198 : ((p0 ∧ p1) → (p1 ∨ p6)) := by
                intro assump_35
                cases assump_35
                case intro assump_36 assump_37 =>
                  apply Or.inl
                  exact assump_37
              let assump_34 := assump_22 assump_198
              apply False.elim assump_34
            case inr assump_17 =>
              have assump_199 : (((p6 ∨ False) → False) → ((p3 ∨ False) ∨ (p6 → p4))) := by
                intro assump_50
                apply Or.inr
                intro assump_53
                have assump_200 : (p6 ∨ False) := by
                  apply Or.inl
                  exact assump_53
                let assump_57 := assump_50 assump_200
                apply False.elim assump_57
              let assump_49 := assump_3 assump_199
              have assump_201 : ((p0 ∧ p1) → (p1 ∨ p6)) := by
                intro assump_62
                cases assump_62
                case intro assump_63 assump_64 =>
                  apply Or.inl
                  exact assump_64
              let assump_61 := assump_49 assump_201
              apply False.elim assump_61
        case inr assump_9 =>
          cases assump_5
          case intro assump_74 assump_75 =>
            cases assump_75
            case inl assump_78 =>
              have assump_202 : (((p6 ∨ False) → False) → ((p3 ∨ False) ∨ (p6 → p4))) := by
                intro assump_85
                apply Or.inr
                intro assump_88
                have assump_203 : (p6 ∨ False) := by
                  apply Or.inl
                  exact assump_88
                let assump_92 := assump_85 assump_203
                apply False.elim assump_92
              let assump_84 := assump_3 assump_202
              have assump_204 : ((p0 ∧ p1) → (p1 ∨ p6)) := by
                intro assump_97
                cases assump_97
                case intro assump_98 assump_99 =>
                  apply Or.inl
                  exact assump_99
              let assump_96 := assump_84 assump_204
              apply False.elim assump_96
            case inr assump_79 =>
              have assump_205 : (((p6 ∨ False) → False) → ((p3 ∨ False) ∨ (p6 → p4))) := by
                intro assump_112
                apply Or.inr
                intro assump_115
                have assump_206 : (p6 ∨ False) := by
                  apply Or.inl
                  exact assump_115
                let assump_119 := assump_112 assump_206
                apply False.elim assump_119
              let assump_111 := assump_3 assump_205
              have assump_207 : ((p0 ∧ p1) → (p1 ∨ p6)) := by
                intro assump_124
                cases assump_124
                case intro assump_125 assump_126 =>
                  apply Or.inl
                  exact assump_126
              let assump_123 := assump_111 assump_207
              apply False.elim assump_123
      case inr assump_7 =>
        cases assump_5
        case intro assump_136 assump_137 =>
          cases assump_137
          case inl assump_140 =>
            have assump_208 : (((p6 ∨ False) → False) → ((p3 ∨ False) ∨ (p6 → p4))) := by
              intro assump_147
              apply Or.inr
              intro assump_150
              have assump_209 : (p6 ∨ False) := by
                apply Or.inl
                exact assump_150
              let assump_154 := assump_147 assump_209
              apply False.elim assump_154
            let assump_146 := assump_3 assump_208
            have assump_210 : ((p0 ∧ p1) → (p1 ∨ p6)) := by
              intro assump_159
              cases assump_159
              case intro assump_160 assump_161 =>
                apply Or.inl
                exact assump_161
            let assump_158 := assump_146 assump_210
            apply False.elim assump_158
          case inr assump_141 =>
            have assump_211 : (((p6 ∨ False) → False) → ((p3 ∨ False) ∨ (p6 → p4))) := by
              intro assump_174
              apply Or.inr
              intro assump_177
              have assump_212 : (p6 ∨ False) := by
                apply Or.inl
                exact assump_177
              let assump_181 := assump_174 assump_212
              apply False.elim assump_181
            let assump_173 := assump_3 assump_211
            have assump_213 : ((p0 ∧ p1) → (p1 ∨ p6)) := by
              intro assump_186
              cases assump_186
              case intro assump_187 assump_188 =>
                apply Or.inl
                exact assump_188
            let assump_185 := assump_173 assump_213
            apply False.elim assump_185


variable (p5 p3 p4 p1 p7 p6 : Prop)
theorem file52_85084 : (((((p7 → p4) ∧ (p5 → False)) → ((p1 → False) → False)) → False) → ((((p4 ∨ True) → (p5 → False)) ∨ ((p6 → False) → (False → p4))) ∧ (((p1 ∨ p3) → False) → ((p1 ∧ p7) → False)))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_86 : (((p7 → p4) ∧ (p5 → False)) → ((p1 → False) → False)) := by
      intro assump_15
      intro assump_16
      cases assump_15
      case intro assump_19 assump_20 =>
        have assump_87 : p5 := by
          exact assump_5
        let assump_25 := assump_20 assump_87
        apply False.elim assump_25
    let assump_14 := assump_1 assump_86
    apply False.elim assump_14
  case inr assump_9 =>
    have assump_88 : (((p7 → p4) ∧ (p5 → False)) → ((p1 → False) → False)) := by
      intro assump_36
      intro assump_37
      cases assump_36
      case intro assump_40 assump_41 =>
        have assump_89 : p5 := by
          exact assump_5
        let assump_46 := assump_41 assump_89
        apply False.elim assump_46
    let assump_35 := assump_1 assump_88
    apply False.elim assump_35
  intro assump_53
  intro assump_54
  cases assump_54
  case intro assump_55 assump_56 =>
    have assump_90 : (((p7 → p4) ∧ (p5 → False)) → ((p1 → False) → False)) := by
      intro assump_66
      intro assump_67
      cases assump_66
      case intro assump_70 assump_71 =>
        have assump_91 : p1 := by
          exact assump_55
        let assump_79 := assump_67 assump_91
        apply False.elim assump_79
    let assump_65 := assump_1 assump_90
    apply False.elim assump_65


variable (p5 p7 p2 p0 p1 p4 p6 : Prop)
theorem file52_86761 : (((((p6 ∧ p2) → (p5 ∧ p0)) ∧ ((p4 ∨ p1) ∨ (p1 → p5))) → (((True ∨ p1) → False) → ((p6 ∨ p4) ∧ (p5 ∧ p6)))) ∨ ((((p1 → False) → (True → False)) → ((p6 → False) ∨ (False ∧ p1))) → (((p1 ∨ p6) ∧ (p6 → False)) ∧ ((p1 ∨ p7) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inr
        exact assump_11
      case inr assump_12 =>
        have assump_99 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_19 := assump_2 assump_99
        apply False.elim assump_19
    case inr assump_10 =>
      have assump_100 : (True ∨ p1) := by
        apply Or.inl
        apply True.intro
      let assump_27 := assump_2 assump_100
      apply False.elim assump_27
  apply And.intro
  cases assump_1
  case intro assump_33 assump_34 =>
    cases assump_34
    case inl assump_37 =>
      cases assump_37
      case inl assump_39 =>
        have assump_101 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_45 := assump_2 assump_101
        apply False.elim assump_45
      case inr assump_40 =>
        have assump_102 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_53 := assump_2 assump_102
        apply False.elim assump_53
    case inr assump_38 =>
      have assump_103 : (True ∨ p1) := by
        apply Or.inl
        apply True.intro
      let assump_61 := assump_2 assump_103
      apply False.elim assump_61
  cases assump_1
  case intro assump_67 assump_68 =>
    cases assump_68
    case inl assump_71 =>
      cases assump_71
      case inl assump_73 =>
        have assump_104 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_79 := assump_2 assump_104
        apply False.elim assump_79
      case inr assump_74 =>
        have assump_105 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_87 := assump_2 assump_105
        apply False.elim assump_87
    case inr assump_72 =>
      have assump_106 : (True ∨ p1) := by
        apply Or.inl
        apply True.intro
      let assump_95 := assump_2 assump_106
      apply False.elim assump_95


variable (p0 p6 p3 p2 p4 p5 p7 p1 : Prop)
theorem file52_89158 : ((((((p1 → True) → False) → ((p6 → False) ∨ (p6 ∧ p1))) ∧ (((p0 → False) ∨ (True ∧ p2)) ∨ ((p7 → False) ∧ (False ∨ p4)))) ∧ ((((p5 → False) ∨ (p3 ∨ p2)) ∧ ((p2 ∧ p4) ∧ (p5 ∨ p5))) ∧ (((p5 → False) → False) ∧ ((False ∧ p4) ∧ (False ∧ p1))))) → False) := by
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_8
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_21
              case inl assump_23 =>
                cases assump_22
                case intro assump_27 assump_28 =>
                  cases assump_27
                  case intro assump_29 assump_30 =>
                    cases assump_28
                    case inl assump_35 =>
                      cases assump_20
                      case intro assump_39 assump_40 =>
                        cases assump_40
                        case intro assump_43 assump_44 =>
                          cases assump_43
                          case intro assump_45 assump_46 =>
                            apply False.elim assump_45
                    case inr assump_36 =>
                      cases assump_20
                      case intro assump_51 assump_52 =>
                        cases assump_52
                        case intro assump_55 assump_56 =>
                          cases assump_55
                          case intro assump_57 assump_58 =>
                            apply False.elim assump_57
              case inr assump_24 =>
                cases assump_24
                case inl assump_61 =>
                  cases assump_22
                  case intro assump_65 assump_66 =>
                    cases assump_65
                    case intro assump_67 assump_68 =>
                      cases assump_66
                      case inl assump_73 =>
                        cases assump_20
                        case intro assump_77 assump_78 =>
                          cases assump_78
                          case intro assump_81 assump_82 =>
                            cases assump_81
                            case intro assump_83 assump_84 =>
                              apply False.elim assump_83
                      case inr assump_74 =>
                        cases assump_20
                        case intro assump_89 assump_90 =>
                          cases assump_90
                          case intro assump_93 assump_94 =>
                            cases assump_93
                            case intro assump_95 assump_96 =>
                              apply False.elim assump_95
                case inr assump_62 =>
                  cases assump_22
                  case intro assump_101 assump_102 =>
                    cases assump_101
                    case intro assump_103 assump_104 =>
                      cases assump_102
                      case inl assump_109 =>
                        cases assump_20
                        case intro assump_113 assump_114 =>
                          cases assump_114
                          case intro assump_117 assump_118 =>
                            cases assump_117
                            case intro assump_119 assump_120 =>
                              apply False.elim assump_119
                      case inr assump_110 =>
                        cases assump_20
                        case intro assump_125 assump_126 =>
                          cases assump_126
                          case intro assump_129 assump_130 =>
                            cases assump_129
                            case intro assump_131 assump_132 =>
                              apply False.elim assump_131
        case inr assump_16 =>
          cases assump_16
          case intro assump_135 assump_136 =>
            cases assump_8
            case intro assump_141 assump_142 =>
              cases assump_141
              case intro assump_143 assump_144 =>
                cases assump_143
                case inl assump_145 =>
                  cases assump_144
                  case intro assump_149 assump_150 =>
                    cases assump_149
                    case intro assump_151 assump_152 =>
                      cases assump_150
                      case inl assump_157 =>
                        cases assump_142
                        case intro assump_161 assump_162 =>
                          cases assump_162
                          case intro assump_165 assump_166 =>
                            cases assump_165
                            case intro assump_167 assump_168 =>
                              apply False.elim assump_167
                      case inr assump_158 =>
                        cases assump_142
                        case intro assump_173 assump_174 =>
                          cases assump_174
                          case intro assump_177 assump_178 =>
                            cases assump_177
                            case intro assump_179 assump_180 =>
                              apply False.elim assump_179
                case inr assump_146 =>
                  cases assump_146
                  case inl assump_183 =>
                    cases assump_144
                    case intro assump_187 assump_188 =>
                      cases assump_187
                      case intro assump_189 assump_190 =>
                        cases assump_188
                        case inl assump_195 =>
                          cases assump_142
                          case intro assump_199 assump_200 =>
                            cases assump_200
                            case intro assump_203 assump_204 =>
                              cases assump_203
                              case intro assump_205 assump_206 =>
                                apply False.elim assump_205
                        case inr assump_196 =>
                          cases assump_142
                          case intro assump_211 assump_212 =>
                            cases assump_212
                            case intro assump_215 assump_216 =>
                              cases assump_215
                              case intro assump_217 assump_218 =>
                                apply False.elim assump_217
                  case inr assump_184 =>
                    cases assump_144
                    case intro assump_223 assump_224 =>
                      cases assump_223
                      case intro assump_225 assump_226 =>
                        cases assump_224
                        case inl assump_231 =>
                          cases assump_142
                          case intro assump_235 assump_236 =>
                            cases assump_236
                            case intro assump_239 assump_240 =>
                              cases assump_239
                              case intro assump_241 assump_242 =>
                                apply False.elim assump_241
                        case inr assump_232 =>
                          cases assump_142
                          case intro assump_247 assump_248 =>
                            cases assump_248
                            case intro assump_251 assump_252 =>
                              cases assump_251
                              case intro assump_253 assump_254 =>
                                apply False.elim assump_253
      case inr assump_14 =>
        cases assump_14
        case intro assump_257 assump_258 =>
          cases assump_258
          case inl assump_261 =>
            apply False.elim assump_261
          case inr assump_262 =>
            cases assump_8
            case intro assump_267 assump_268 =>
              cases assump_267
              case intro assump_269 assump_270 =>
                cases assump_269
                case inl assump_271 =>
                  cases assump_270
                  case intro assump_275 assump_276 =>
                    cases assump_275
                    case intro assump_277 assump_278 =>
                      cases assump_276
                      case inl assump_283 =>
                        cases assump_268
                        case intro assump_287 assump_288 =>
                          cases assump_288
                          case intro assump_291 assump_292 =>
                            cases assump_291
                            case intro assump_293 assump_294 =>
                              apply False.elim assump_293
                      case inr assump_284 =>
                        cases assump_268
                        case intro assump_299 assump_300 =>
                          cases assump_300
                          case intro assump_303 assump_304 =>
                            cases assump_303
                            case intro assump_305 assump_306 =>
                              apply False.elim assump_305
                case inr assump_272 =>
                  cases assump_272
                  case inl assump_309 =>
                    cases assump_270
                    case intro assump_313 assump_314 =>
                      cases assump_313
                      case intro assump_315 assump_316 =>
                        cases assump_314
                        case inl assump_321 =>
                          cases assump_268
                          case intro assump_325 assump_326 =>
                            cases assump_326
                            case intro assump_329 assump_330 =>
                              cases assump_329
                              case intro assump_331 assump_332 =>
                                apply False.elim assump_331
                        case inr assump_322 =>
                          cases assump_268
                          case intro assump_337 assump_338 =>
                            cases assump_338
                            case intro assump_341 assump_342 =>
                              cases assump_341
                              case intro assump_343 assump_344 =>
                                apply False.elim assump_343
                  case inr assump_310 =>
                    cases assump_270
                    case intro assump_349 assump_350 =>
                      cases assump_349
                      case intro assump_351 assump_352 =>
                        cases assump_350
                        case inl assump_357 =>
                          cases assump_268
                          case intro assump_361 assump_362 =>
                            cases assump_362
                            case intro assump_365 assump_366 =>
                              cases assump_365
                              case intro assump_367 assump_368 =>
                                apply False.elim assump_367
                        case inr assump_358 =>
                          cases assump_268
                          case intro assump_373 assump_374 =>
                            cases assump_374
                            case intro assump_377 assump_378 =>
                              cases assump_377
                              case intro assump_379 assump_380 =>
                                apply False.elim assump_379


variable (p4 p0 p3 p2 p6 p1 p5 p7 : Prop)
theorem file52_100738 : (((((p5 ∧ p6) ∧ (False ∧ True)) ∧ ((True ∧ p0) → False)) → (((p1 → p0) → False) → ((True ∨ p2) → (p1 → p7)))) → ((((p2 ∨ p3) ∨ (p0 → False)) → ((p0 → False) ∧ (p1 ∨ False))) → (((False ∧ p4) → False) ∨ ((False → False) → (p4 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p2 p4 p5 p1 p0 p7 p3 : Prop)
theorem file52_101192 : (((((p2 → False) ∧ (p3 ∨ p4)) ∧ ((p1 → False) ∨ (False → p5))) → (((False → p7) ∨ (p7 ∨ p0)) ∨ ((p2 → False) ∨ (p1 ∨ True)))) ∨ ((((p7 → False) ∧ (False ∨ p2)) → False) ∧ (((True → False) → False) ∨ ((p0 ∨ p0) → False)))) := by
  apply Or.inl
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_16
      case inl assump_19 =>
        cases assump_14
        case inl assump_23 =>
          apply Or.inl
          apply Or.inl
          intro assump_27
          apply False.elim assump_27
        case inr assump_24 =>
          apply Or.inl
          apply Or.inl
          intro assump_32
          apply False.elim assump_32
      case inr assump_20 =>
        cases assump_14
        case inl assump_37 =>
          apply Or.inl
          apply Or.inl
          intro assump_41
          apply False.elim assump_41
        case inr assump_38 =>
          apply Or.inl
          apply Or.inl
          intro assump_46
          apply False.elim assump_46


variable (p5 p6 p3 p1 p2 p4 : Prop)
theorem file52_102307 : (((((p3 ∨ p1) → False) → ((p3 ∨ p5) ∨ (p6 → False))) → False) → ((((False → False) ∧ (False ∧ p3)) → ((False ∧ p2) → False)) ∧ (((p1 ∧ p6) → (p5 ∧ p2)) ∧ ((False → False) ∨ (p6 → p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4
  apply And.intro
  intro assump_8
  apply And.intro
  cases assump_8
  case intro assump_9 assump_10 =>
    have assump_60 : (((p3 ∨ p1) → False) → ((p3 ∨ p5) ∨ (p6 → False))) := by
      intro assump_18
      apply Or.inr
      intro assump_21
      have assump_61 : (p3 ∨ p1) := by
        apply Or.inr
        exact assump_9
      let assump_25 := assump_18 assump_61
      apply False.elim assump_25
    let assump_17 := assump_1 assump_60
    apply False.elim assump_17
  cases assump_8
  case intro assump_32 assump_33 =>
    have assump_62 : (((p3 ∨ p1) → False) → ((p3 ∨ p5) ∨ (p6 → False))) := by
      intro assump_41
      apply Or.inr
      intro assump_44
      have assump_63 : (p3 ∨ p1) := by
        apply Or.inr
        exact assump_32
      let assump_48 := assump_41 assump_63
      apply False.elim assump_48
    let assump_40 := assump_1 assump_62
    apply False.elim assump_40
  apply Or.inl
  intro assump_57
  apply False.elim assump_57


variable (p5 p1 p6 p0 p4 p2 p7 p3 : Prop)
theorem file52_103679 : (((((p4 → False) ∧ (p2 ∧ p7)) ∨ ((p4 → False) ∧ (p7 → p4))) → (((p5 → False) → False) ∨ ((p7 ∧ p7) ∨ (p5 → False)))) → ((((p3 ∧ False) ∧ (p1 ∨ p5)) ∧ ((p0 → True) ∨ (p7 ∨ p4))) → (((p0 ∨ p2) ∧ (p6 → False)) ∧ ((p1 → p1) ∧ (p2 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8
  intro assump_13
  cases assump_2
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
  apply And.intro
  intro assump_26
  cases assump_2
  case intro assump_29 assump_30 =>
    cases assump_29
    case intro assump_31 assump_32 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        apply False.elim assump_34
  intro assump_39
  cases assump_2
  case intro assump_42 assump_43 =>
    cases assump_42
    case intro assump_44 assump_45 =>
      cases assump_44
      case intro assump_46 assump_47 =>
        apply False.elim assump_47


variable (p3 p0 p4 p5 p2 p7 : Prop)
theorem file52_104949 : ((((((False → p3) → False) ∧ ((p7 ∧ p7) ∨ (p2 → p5))) → (((p0 ∧ p4) → False) → ((p0 ∨ p4) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_51 : ((((False → p3) → False) ∧ ((p7 ∧ p7) ∨ (p2 → p5))) → (((p0 ∧ p4) → False) → ((p0 ∨ p4) ∨ (p0 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply Or.inr
          intro assump_21
          have assump_52 : (False → p3) := by
            intro assump_28
            apply False.elim assump_28
          let assump_27 := assump_9 assump_52
          apply False.elim assump_27
      case inr assump_14 =>
        apply Or.inr
        intro assump_36
        have assump_53 : (False → p3) := by
          intro assump_42
          apply False.elim assump_42
        let assump_41 := assump_9 assump_53
        apply False.elim assump_41
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p2 p4 p6 p3 p5 : Prop)
theorem file52_106065 : (((((p2 → False) ∧ (p3 ∧ p4)) ∧ ((False ∨ p2) ∧ (p5 → p4))) → (((p4 → False) → False) ∨ ((True → False) → False))) ∨ ((((p2 ∧ True) ∨ (p2 ∨ p3)) → ((False → p6) → False)) → False)) := by
  apply Or.inl
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
            apply False.elim assump_16
          case inr assump_17 =>
            apply Or.inl
            intro assump_24
            have assump_31 : p4 := by
              exact assump_9
            let assump_27 := assump_24 assump_31
            apply False.elim assump_27


variable (p6 p2 p5 p7 p1 : Prop)
theorem file52_106908 : ((((((True ∨ p7) → (True → False)) ∧ ((p2 → False) ∨ (p1 → False))) → (((p5 ∧ p6) ∨ (p5 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_64 : ((((True ∨ p7) → (True → False)) ∧ ((p2 → False) ∨ (p1 → False))) → (((p5 ∧ p6) ∨ (p5 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_5
        case intro assump_15 assump_16 =>
          cases assump_16
          case inl assump_19 =>
            have assump_65 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_24 := assump_15 assump_65
            have assump_66 : True := by
              apply True.intro
            let assump_25 := assump_24 assump_66
            apply False.elim assump_25
          case inr assump_20 =>
            have assump_67 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_32 := assump_15 assump_67
            have assump_68 : True := by
              apply True.intro
            let assump_33 := assump_32 assump_68
            apply False.elim assump_33
    case inr assump_8 =>
      cases assump_5
      case intro assump_39 assump_40 =>
        cases assump_40
        case inl assump_43 =>
          have assump_69 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_48 := assump_39 assump_69
          have assump_70 : True := by
            apply True.intro
          let assump_49 := assump_48 assump_70
          apply False.elim assump_49
        case inr assump_44 =>
          have assump_71 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_56 := assump_39 assump_71
          have assump_72 : True := by
            apply True.intro
          let assump_57 := assump_56 assump_72
          apply False.elim assump_57
  let assump_4 := assump_1 assump_64
  apply False.elim assump_4


variable (p1 p5 p2 p7 p0 : Prop)
theorem file52_108997 : ((((((True ∧ p2) ∧ (p1 ∨ False)) ∧ ((True ∨ False) ∧ (p2 → p0))) ∨ (((p5 → False) ∧ (False ∧ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_17 : ((((True ∧ p2) ∧ (p1 ∨ False)) ∧ ((True ∨ False) ∧ (p2 → p0))) ∨ (((p5 → False) ∧ (False ∧ p7)) → False)) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p2 p7 p0 p3 p1 p4 : Prop)
theorem file52_109589 : (((((True → False) → (p4 ∨ p2)) → False) ∧ (((p4 → False) ∧ (p1 ∧ p1)) ∧ ((p0 → p1) → False))) → ((((p1 ∨ False) ∧ (p4 ∧ p2)) → ((True ∨ p7) → False)) ∧ (((p7 → p1) ∧ (True → p3)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          cases assump_1
          case intro assump_20 assump_21 =>
            cases assump_21
            case intro assump_24 assump_25 =>
              cases assump_24
              case intro assump_26 assump_27 =>
                cases assump_27
                case intro assump_30 assump_31 =>
                  have assump_120 : (p0 → p1) := by
                    intro assump_39
                    exact assump_31
                  let assump_38 := assump_25 assump_120
                  apply False.elim assump_38
      case inr assump_11 =>
        apply False.elim assump_11
  case inr assump_5 =>
    cases assump_2
    case intro assump_49 assump_50 =>
      cases assump_49
      case inl assump_51 =>
        cases assump_50
        case intro assump_55 assump_56 =>
          cases assump_1
          case intro assump_61 assump_62 =>
            cases assump_62
            case intro assump_65 assump_66 =>
              cases assump_65
              case intro assump_67 assump_68 =>
                cases assump_68
                case intro assump_71 assump_72 =>
                  have assump_121 : (p0 → p1) := by
                    intro assump_80
                    exact assump_72
                  let assump_79 := assump_66 assump_121
                  apply False.elim assump_79
      case inr assump_52 =>
        apply False.elim assump_52
  intro assump_88
  cases assump_88
  case intro assump_89 assump_90 =>
    cases assump_1
    case intro assump_95 assump_96 =>
      cases assump_96
      case intro assump_99 assump_100 =>
        cases assump_99
        case intro assump_101 assump_102 =>
          cases assump_102
          case intro assump_105 assump_106 =>
            have assump_122 : (p0 → p1) := by
              intro assump_114
              exact assump_106
            let assump_113 := assump_100 assump_122
            apply False.elim assump_113


variable (p5 p0 p2 p1 p6 p4 : Prop)
theorem file52_112035 : ((((((p4 ∧ False) ∧ (p2 ∨ p0)) → False) ∨ (((p0 → False) ∨ (p2 ∧ p1)) ∧ ((True → p6) ∧ (p6 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p4 ∧ False) ∧ (p2 ∨ p0)) → False) ∨ (((p0 → False) ∨ (p2 ∧ p1)) ∧ ((True → p6) ∧ (p6 ∧ p5)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p3 p7 p5 p0 p6 p4 p1 : Prop)
theorem file52_112611 : (((((p4 → False) ∨ (False ∧ p5)) → ((p3 → False) → (p7 ∨ True))) ∨ (((p1 → False) → False) → ((True → False) → (p6 ∧ p0)))) ∨ ((((p6 ∧ p0) ∧ (p0 ∨ False)) → False) ∧ (((p4 ∧ False) → (p7 ∨ True)) → ((p4 → False) ∧ (p5 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inr
    apply True.intro
  case inr assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply False.elim assump_9


variable (p4 p2 p0 p3 p6 : Prop)
theorem file52_113155 : (((((False ∧ False) ∧ (p3 → False)) ∧ ((p4 → False) ∧ (p4 → False))) ∧ (((p0 ∧ p6) → (p2 → False)) ∧ ((p3 → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8


variable (p5 p0 p4 p6 p2 p7 p1 : Prop)
theorem file52_113640 : ((((((p5 ∨ p2) → (p0 → False)) → False) ∧ (((p7 ∨ p6) ∧ (p1 ∧ p6)) ∨ ((p5 ∧ p4) → (p5 ∧ True)))) ∧ ((((p0 ∨ p1) → False) ∨ ((p2 → False) ∨ (False → False))) ∧ (((p1 ∧ p4) ∨ (p0 ∨ p5)) ∧ ((True ∨ p2) → False)))) → False) := by
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
            cases assump_11
            case intro assump_16 assump_17 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_23
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_30
                      case intro assump_32 assump_33 =>
                        have assump_374 : (True ∨ p2) := by
                          apply Or.inl
                          apply True.intro
                        let assump_40 := assump_29 assump_374
                        apply False.elim assump_40
                    case inr assump_31 =>
                      cases assump_31
                      case inl assump_44 =>
                        have assump_375 : (True ∨ p2) := by
                          apply Or.inl
                          apply True.intro
                        let assump_50 := assump_29 assump_375
                        apply False.elim assump_50
                      case inr assump_45 =>
                        have assump_376 : (True ∨ p2) := by
                          apply Or.inl
                          apply True.intro
                        let assump_58 := assump_29 assump_376
                        apply False.elim assump_58
                case inr assump_25 =>
                  cases assump_25
                  case inl assump_62 =>
                    cases assump_23
                    case intro assump_66 assump_67 =>
                      cases assump_66
                      case inl assump_68 =>
                        cases assump_68
                        case intro assump_70 assump_71 =>
                          have assump_377 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_78 := assump_67 assump_377
                          apply False.elim assump_78
                      case inr assump_69 =>
                        cases assump_69
                        case inl assump_82 =>
                          have assump_378 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_88 := assump_67 assump_378
                          apply False.elim assump_88
                        case inr assump_83 =>
                          have assump_379 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_96 := assump_67 assump_379
                          apply False.elim assump_96
                  case inr assump_63 =>
                    cases assump_23
                    case intro assump_102 assump_103 =>
                      cases assump_102
                      case inl assump_104 =>
                        cases assump_104
                        case intro assump_106 assump_107 =>
                          have assump_380 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_114 := assump_103 assump_380
                          apply False.elim assump_114
                      case inr assump_105 =>
                        cases assump_105
                        case inl assump_118 =>
                          have assump_381 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_124 := assump_103 assump_381
                          apply False.elim assump_124
                        case inr assump_119 =>
                          have assump_382 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_132 := assump_103 assump_382
                          apply False.elim assump_132
          case inr assump_13 =>
            cases assump_11
            case intro assump_138 assump_139 =>
              cases assump_3
              case intro assump_144 assump_145 =>
                cases assump_144
                case inl assump_146 =>
                  cases assump_145
                  case intro assump_150 assump_151 =>
                    cases assump_150
                    case inl assump_152 =>
                      cases assump_152
                      case intro assump_154 assump_155 =>
                        have assump_383 : (True ∨ p2) := by
                          apply Or.inl
                          apply True.intro
                        let assump_162 := assump_151 assump_383
                        apply False.elim assump_162
                    case inr assump_153 =>
                      cases assump_153
                      case inl assump_166 =>
                        have assump_384 : (True ∨ p2) := by
                          apply Or.inl
                          apply True.intro
                        let assump_172 := assump_151 assump_384
                        apply False.elim assump_172
                      case inr assump_167 =>
                        have assump_385 : (True ∨ p2) := by
                          apply Or.inl
                          apply True.intro
                        let assump_180 := assump_151 assump_385
                        apply False.elim assump_180
                case inr assump_147 =>
                  cases assump_147
                  case inl assump_184 =>
                    cases assump_145
                    case intro assump_188 assump_189 =>
                      cases assump_188
                      case inl assump_190 =>
                        cases assump_190
                        case intro assump_192 assump_193 =>
                          have assump_386 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_200 := assump_189 assump_386
                          apply False.elim assump_200
                      case inr assump_191 =>
                        cases assump_191
                        case inl assump_204 =>
                          have assump_387 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_210 := assump_189 assump_387
                          apply False.elim assump_210
                        case inr assump_205 =>
                          have assump_388 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_218 := assump_189 assump_388
                          apply False.elim assump_218
                  case inr assump_185 =>
                    cases assump_145
                    case intro assump_224 assump_225 =>
                      cases assump_224
                      case inl assump_226 =>
                        cases assump_226
                        case intro assump_228 assump_229 =>
                          have assump_389 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_236 := assump_225 assump_389
                          apply False.elim assump_236
                      case inr assump_227 =>
                        cases assump_227
                        case inl assump_240 =>
                          have assump_390 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_246 := assump_225 assump_390
                          apply False.elim assump_246
                        case inr assump_241 =>
                          have assump_391 : (True ∨ p2) := by
                            apply Or.inl
                            apply True.intro
                          let assump_254 := assump_225 assump_391
                          apply False.elim assump_254
      case inr assump_9 =>
        cases assump_3
        case intro assump_260 assump_261 =>
          cases assump_260
          case inl assump_262 =>
            cases assump_261
            case intro assump_266 assump_267 =>
              cases assump_266
              case inl assump_268 =>
                cases assump_268
                case intro assump_270 assump_271 =>
                  have assump_392 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_278 := assump_267 assump_392
                  apply False.elim assump_278
              case inr assump_269 =>
                cases assump_269
                case inl assump_282 =>
                  have assump_393 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_288 := assump_267 assump_393
                  apply False.elim assump_288
                case inr assump_283 =>
                  have assump_394 : (True ∨ p2) := by
                    apply Or.inl
                    apply True.intro
                  let assump_296 := assump_267 assump_394
                  apply False.elim assump_296
          case inr assump_263 =>
            cases assump_263
            case inl assump_300 =>
              cases assump_261
              case intro assump_304 assump_305 =>
                cases assump_304
                case inl assump_306 =>
                  cases assump_306
                  case intro assump_308 assump_309 =>
                    have assump_395 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_316 := assump_305 assump_395
                    apply False.elim assump_316
                case inr assump_307 =>
                  cases assump_307
                  case inl assump_320 =>
                    have assump_396 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_326 := assump_305 assump_396
                    apply False.elim assump_326
                  case inr assump_321 =>
                    have assump_397 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_334 := assump_305 assump_397
                    apply False.elim assump_334
            case inr assump_301 =>
              cases assump_261
              case intro assump_340 assump_341 =>
                cases assump_340
                case inl assump_342 =>
                  cases assump_342
                  case intro assump_344 assump_345 =>
                    have assump_398 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_352 := assump_341 assump_398
                    apply False.elim assump_352
                case inr assump_343 =>
                  cases assump_343
                  case inl assump_356 =>
                    have assump_399 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_362 := assump_341 assump_399
                    apply False.elim assump_362
                  case inr assump_357 =>
                    have assump_400 : (True ∨ p2) := by
                      apply Or.inl
                      apply True.intro
                    let assump_370 := assump_341 assump_400
                    apply False.elim assump_370


variable (p6 p5 p4 p0 p7 p3 p2 p1 : Prop)
theorem file52_126015 : ((((((p6 → False) ∨ (p6 ∨ False)) ∨ ((p7 ∧ p0) ∧ (p1 ∧ p0))) ∧ (((p2 → False) ∧ (p0 ∨ p4)) → ((p5 → p4) ∨ (p6 → False)))) ∧ ((((p5 ∧ False) → (False → p7)) → ((p7 → p7) ∨ (p3 ∧ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_74 : (((p5 ∧ False) → (False → p7)) → ((p7 → p7) ∨ (p3 ∧ p0))) := by
            intro assump_17
            apply Or.inl
            intro assump_20
            exact assump_20
          let assump_16 := assump_3 assump_74
          apply False.elim assump_16
        case inr assump_9 =>
          cases assump_9
          case inl assump_26 =>
            have assump_75 : (((p5 ∧ False) → (False → p7)) → ((p7 → p7) ∨ (p3 ∧ p0))) := by
              intro assump_35
              apply Or.inl
              intro assump_38
              exact assump_38
            let assump_34 := assump_3 assump_75
            apply False.elim assump_34
          case inr assump_27 =>
            apply False.elim assump_27
      case inr assump_7 =>
        cases assump_7
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            cases assump_47
            case intro assump_54 assump_55 =>
              have assump_76 : (((p5 ∧ False) → (False → p7)) → ((p7 → p7) ∨ (p3 ∧ p0))) := by
                intro assump_65
                apply Or.inl
                intro assump_68
                exact assump_68
              let assump_64 := assump_3 assump_76
              apply False.elim assump_64


variable (p4 p0 p7 p1 p3 p2 : Prop)
theorem file52_127790 : ((((((p1 ∧ p4) → (p1 → p2)) → ((p3 ∧ True) ∨ (p1 ∨ p1))) → False) ∧ ((((p7 ∨ p0) → (p7 → False)) → ((p1 ∨ p2) → (True ∨ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p7 ∨ p0) → (p7 → False)) → ((p1 ∨ p2) → (True ∨ p7))) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        apply Or.inl
        apply True.intro
      case inr assump_12 =>
        apply Or.inl
        apply True.intro
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p2 p1 p0 p7 p6 p5 p4 p3 : Prop)
theorem file52_128441 : (((((False → p0) → (p5 ∨ p4)) ∨ ((p1 ∧ p7) → (p6 → False))) ∧ (((True ∨ True) → False) ∧ ((p4 → p0) ∨ (p7 ∨ True)))) → ((((p3 ∧ p4) → (p2 → False)) ∧ ((p6 → False) → (p6 ∧ True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          cases assump_16
          case inl assump_19 =>
            have assump_73 : (True ∨ True) := by
              apply Or.inl
              apply True.intro
            let assump_24 := assump_15 assump_73
            apply False.elim assump_24
          case inr assump_20 =>
            cases assump_20
            case inl assump_28 =>
              have assump_74 : (True ∨ True) := by
                apply Or.inl
                apply True.intro
              let assump_33 := assump_15 assump_74
              apply False.elim assump_33
            case inr assump_29 =>
              have assump_75 : (True ∨ True) := by
                apply Or.inl
                apply True.intro
              let assump_39 := assump_15 assump_75
              apply False.elim assump_39
      case inr assump_12 =>
        cases assump_10
        case intro assump_45 assump_46 =>
          cases assump_46
          case inl assump_49 =>
            have assump_76 : (True ∨ True) := by
              apply Or.inl
              apply True.intro
            let assump_54 := assump_45 assump_76
            apply False.elim assump_54
          case inr assump_50 =>
            cases assump_50
            case inl assump_58 =>
              have assump_77 : (True ∨ True) := by
                apply Or.inl
                apply True.intro
              let assump_63 := assump_45 assump_77
              apply False.elim assump_63
            case inr assump_59 =>
              have assump_78 : (True ∨ True) := by
                apply Or.inl
                apply True.intro
              let assump_69 := assump_45 assump_78
              apply False.elim assump_69


variable (p0 p2 p1 p4 p3 : Prop)
theorem file52_130626 : (((((False ∧ p2) ∧ (p2 → p4)) → False) → False) → ((((False ∧ p1) ∧ (False ∨ p4)) ∨ ((p2 → False) ∨ (p0 → p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7
  case inr assump_4 =>
    cases assump_4
    case inl assump_11 =>
      have assump_43 : (((False ∧ p2) ∧ (p2 → p4)) → False) := by
        intro assump_18
        cases assump_18
        case intro assump_19 assump_20 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            apply False.elim assump_21
      let assump_17 := assump_1 assump_43
      apply False.elim assump_17
    case inr assump_12 =>
      have assump_44 : (((False ∧ p2) ∧ (p2 → p4)) → False) := by
        intro assump_33
        cases assump_33
        case intro assump_34 assump_35 =>
          cases assump_34
          case intro assump_36 assump_37 =>
            apply False.elim assump_36
      let assump_32 := assump_1 assump_44
      apply False.elim assump_32


variable (p5 p3 p1 p0 p6 p2 p4 : Prop)
theorem file52_131813 : (((((p4 → p5) → (p5 ∨ True)) → ((False ∨ False) ∧ (p2 ∧ p3))) ∧ (((p4 → p6) ∧ (p5 → p4)) ∧ ((p0 → p5) ∨ (p5 → False)))) → ((((p3 → False) ∨ (True → False)) ∨ ((False ∧ True) → False)) ∨ (((p1 → p4) → (True ∧ p3)) ∨ ((p6 → p1) ∨ (p6 → False))))) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_20
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_24
        case inl assump_31 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_35
          have assump_75 : ((p4 → p5) → (p5 ∨ True)) := by
            intro assump_43
            apply Or.inr
            apply True.intro
          let assump_42 := assump_19 assump_75
          let assump_46 := And.left assump_42
          cases assump_46
          case inl assump_48 =>
            apply False.elim assump_48
          case inr assump_49 =>
            apply False.elim assump_49
        case inr assump_32 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_56
          have assump_76 : ((p4 → p5) → (p5 ∨ True)) := by
            intro assump_64
            apply Or.inr
            apply True.intro
          let assump_63 := assump_19 assump_76
          let assump_67 := And.left assump_63
          cases assump_67
          case inl assump_69 =>
            apply False.elim assump_69
          case inr assump_70 =>
            apply False.elim assump_70


variable (p7 p6 : Prop)
theorem file52_133382 : (((((p7 → True) ∧ (p6 ∧ False)) → ((p6 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : (((p7 → True) ∧ (p6 ∧ False)) → ((p6 → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p1 p6 p2 : Prop)
theorem file52_133872 : (((((True → False) → (False → p1)) ∨ ((p2 ∧ p6) → (p7 → False))) → False) → ((((p2 → False) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_15 : (((True → False) → (False → p1)) ∨ ((p2 ∧ p6) → (p7 → False))) := by
    apply Or.inl
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_7 := assump_1 assump_15
  apply False.elim assump_7


variable (p3 p5 p0 p6 p7 : Prop)
theorem file52_134327 : (((((True → p3) ∨ (False → False)) → ((p7 → False) → (True ∨ True))) → False) → ((((p6 → False) → (True → False)) ∨ ((p0 ∧ p7) ∧ (p5 ∨ p3))) ∧ (((p6 ∧ p6) → False) ∧ ((p5 → False) ∧ (p0 ∨ p7))))) := by
  intro assump_9
  apply And.intro
  apply Or.inl
  intro assump_12
  intro assump_13
  have assump_91 : (((True → p3) ∨ (False → False)) → ((p7 → False) → (True ∨ True))) := by
    intro assump_20
    intro assump_21
    cases assump_20
    case inl assump_24 =>
      apply Or.inl
      apply True.intro
    case inr assump_25 =>
      apply Or.inl
      apply True.intro
  let assump_19 := assump_9 assump_91
  apply False.elim assump_19
  apply And.intro
  intro assump_33
  cases assump_33
  case intro assump_34 assump_35 =>
    have assump_92 : (((True → p3) ∨ (False → False)) → ((p7 → False) → (True ∨ True))) := by
      intro assump_43
      intro assump_44
      cases assump_43
      case inl assump_47 =>
        apply Or.inl
        apply True.intro
      case inr assump_48 =>
        apply Or.inl
        apply True.intro
    let assump_42 := assump_9 assump_92
    apply False.elim assump_42
  apply And.intro
  intro assump_56
  have assump_93 : (((True → p3) ∨ (False → False)) → ((p7 → False) → (True ∨ True))) := by
    intro assump_62
    intro assump_63
    cases assump_62
    case inl assump_66 =>
      apply Or.inl
      apply True.intro
    case inr assump_67 =>
      apply Or.inl
      apply True.intro
  let assump_61 := assump_9 assump_93
  apply False.elim assump_61
  have assump_94 : (((True → p3) ∨ (False → False)) → ((p7 → False) → (True ∨ True))) := by
    intro assump_78
    intro assump_79
    cases assump_78
    case inl assump_82 =>
      apply Or.inl
      apply True.intro
    case inr assump_83 =>
      apply Or.inl
      apply True.intro
  let assump_77 := assump_9 assump_94
  apply False.elim assump_77


variable (p5 p3 p4 p0 p7 p2 p1 p6 : Prop)
theorem file52_136251 : ((((((p2 → p7) ∨ (True ∨ p2)) ∧ ((p6 → p2) → (p5 ∧ p3))) → (((p6 ∨ p0) → (p7 ∧ p5)) ∧ ((p5 ∧ True) → False))) ∧ ((((p7 ∧ p6) ∨ (p5 ∨ p2)) → ((p0 ∧ p6) → False)) ∧ (((p4 ∧ p3) → (p1 ∨ p4)) → False))) → False) := by
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_26 : ((p4 ∧ p3) → (p1 ∨ p4)) := by
        intro assump_16
        cases assump_16
        case intro assump_17 assump_18 =>
          apply Or.inr
          exact assump_17
      let assump_15 := assump_10 assump_26
      apply False.elim assump_15


variable (p1 p4 p7 p2 p6 p5 p0 p3 : Prop)
theorem file52_136923 : (((((p1 ∨ p0) ∨ (p4 ∧ p2)) ∨ ((True → False) → False)) ∨ (((True ∨ True) ∧ (p3 ∧ p4)) ∨ ((p3 ∨ p7) ∨ (False ∧ False)))) ∨ ((((p5 → False) ∧ (True → p4)) ∨ ((p2 → False) ∨ (p7 → False))) ∧ (((p6 ∨ p2) → (p4 ∧ p3)) ∧ ((p2 → False) → (p7 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p3 p0 p5 p1 : Prop)
theorem file52_137407 : ((((((False ∧ p0) ∨ (p3 → False)) → ((p1 ∨ p0) ∨ (False → False))) ∧ (((p4 → p4) → False) → ((p5 ∧ p5) ∧ (p3 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_48 : ((((False ∧ p0) ∨ (p3 → False)) → ((p1 ∨ p0) ∨ (False → False))) ∧ (((p4 → p4) → False) → ((p5 ∧ p5) ∧ (p3 ∨ p0)))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    case inr assump_7 =>
      apply Or.inr
      intro assump_14
      apply False.elim assump_14
    intro assump_17
    apply And.intro
    apply And.intro
    have assump_49 : (p4 → p4) := by
      intro assump_21
      exact assump_21
    let assump_20 := assump_17 assump_49
    apply False.elim assump_20
    have assump_50 : (p4 → p4) := by
      intro assump_30
      exact assump_30
    let assump_29 := assump_17 assump_50
    apply False.elim assump_29
    have assump_51 : (p4 → p4) := by
      intro assump_39
      exact assump_39
    let assump_38 := assump_17 assump_51
    apply False.elim assump_38
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p3 p0 p6 p5 p4 p1 : Prop)
theorem file52_138626 : (((((p5 ∨ p4) ∨ (False ∨ p1)) → False) ∧ (((p1 ∨ p6) ∨ (p1 → p6)) → False)) → ((((p6 → False) ∧ (False ∨ p0)) ∨ ((p6 → p5) → (p4 → False))) ∧ (((p3 → False) → False) → ((False → False) ∨ (p1 ∨ p4))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_16
    intro assump_17
    have assump_50 : ((p1 ∨ p6) ∨ (p1 → p6)) := by
      apply Or.inr
      intro assump_25
      have assump_51 : ((p1 ∨ p6) ∨ (p1 → p6)) := by
        apply Or.inl
        apply Or.inl
        exact assump_25
      let assump_31 := assump_3 assump_51
      apply False.elim assump_31
    let assump_24 := assump_3 assump_50
    apply False.elim assump_24
  intro assump_38
  cases assump_1
  case intro assump_41 assump_42 =>
    apply Or.inl
    intro assump_47
    apply False.elim assump_47


variable (p0 p2 : Prop)
theorem file52_139520 : ((((((p2 ∨ p2) → (False → False)) → False) → (((p0 → False) → (False → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p2 ∨ p2) → (False → False)) → False) → (((p0 → False) → (False → False)) → False)) := by
    intro assump_5
    intro assump_6
    have assump_23 : ((p2 ∨ p2) → (False → False)) := by
      intro assump_12
      intro assump_13
      apply False.elim assump_13
    let assump_11 := assump_5 assump_23
    apply False.elim assump_11
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p3 p6 p0 p1 p2 p5 p7 : Prop)
theorem file52_140133 : (((((False ∧ p5) → (p2 ∨ p6)) ∧ ((p6 ∨ p2) ∧ (False ∧ p0))) → (((p5 → False) ∨ (p1 → p5)) ∧ ((p5 → p5) → (p5 → p3)))) ∨ ((((p6 ∨ p6) → False) → False) ∨ (((p1 ∨ p0) ∨ (p3 → p1)) → ((p6 → p3) ∨ (False ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      case inr assump_9 =>
        cases assump_7
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
  intro assump_22
  intro assump_23
  cases assump_1
  case intro assump_28 assump_29 =>
    cases assump_29
    case intro assump_32 assump_33 =>
      cases assump_32
      case inl assump_34 =>
        cases assump_33
        case intro assump_38 assump_39 =>
          apply False.elim assump_38
      case inr assump_35 =>
        cases assump_33
        case intro assump_44 assump_45 =>
          apply False.elim assump_44


variable (p5 p0 p7 p6 p2 : Prop)
theorem file52_141272 : (((((False ∧ p5) → (True → False)) ∨ ((p6 → p0) → False)) → (((p2 → p2) → False) ∧ ((p6 ∨ p6) → (False ∧ p7)))) → False) := by
  intro assump_9
  have assump_29 : (((False ∧ p5) → (True → False)) ∨ ((p6 → p0) → False)) := by
    apply Or.inl
    intro assump_13
    intro assump_14
    cases assump_13
    case intro assump_17 assump_18 =>
      apply False.elim assump_17
  let assump_12 := assump_9 assump_29
  let assump_21 := And.left assump_12
  have assump_30 : (p2 → p2) := by
    intro assump_23
    exact assump_23
  let assump_22 := assump_21 assump_30
  apply False.elim assump_22


variable (p3 p5 p4 p6 p2 p1 p0 p7 : Prop)
theorem file52_141930 : ((((((p3 → p5) ∨ (p5 ∧ p0)) ∧ ((p7 ∧ p2) ∧ (True ∧ p6))) → (((p4 ∧ p7) → (p2 → p6)) ∧ ((p2 → p3) → (p4 → p3)))) → ((((p1 ∧ p1) ∨ (True ∨ p3)) → False) ∧ (((p6 ∧ p5) → (p4 ∨ False)) ∨ ((p4 → False) ∨ (p4 ∧ p6))))) → False) := by
  intro assump_72
  have assump_191 : ((((p3 → p5) ∨ (p5 ∧ p0)) ∧ ((p7 ∧ p2) ∧ (True ∧ p6))) → (((p4 ∧ p7) → (p2 → p6)) ∧ ((p2 → p3) → (p4 → p3)))) := by
    intro assump_76
    apply And.intro
    intro assump_77
    intro assump_78
    cases assump_77
    case intro assump_81 assump_82 =>
      cases assump_76
      case intro assump_87 assump_88 =>
        cases assump_87
        case inl assump_89 =>
          cases assump_88
          case intro assump_93 assump_94 =>
            cases assump_93
            case intro assump_95 assump_96 =>
              cases assump_94
              case intro assump_101 assump_102 =>
                exact assump_102
        case inr assump_90 =>
          cases assump_90
          case intro assump_107 assump_108 =>
            cases assump_88
            case intro assump_113 assump_114 =>
              cases assump_113
              case intro assump_115 assump_116 =>
                cases assump_114
                case intro assump_121 assump_122 =>
                  exact assump_122
    intro assump_127
    intro assump_128
    cases assump_76
    case intro assump_133 assump_134 =>
      cases assump_133
      case inl assump_135 =>
        cases assump_134
        case intro assump_139 assump_140 =>
          cases assump_139
          case intro assump_141 assump_142 =>
            cases assump_140
            case intro assump_147 assump_148 =>
              have assump_192 : p2 := by
                exact assump_142
              let assump_157 := assump_127 assump_192
              exact assump_157
      case inr assump_136 =>
        cases assump_136
        case intro assump_159 assump_160 =>
          cases assump_134
          case intro assump_165 assump_166 =>
            cases assump_165
            case intro assump_167 assump_168 =>
              cases assump_166
              case intro assump_173 assump_174 =>
                have assump_193 : p2 := by
                  exact assump_168
                let assump_184 := assump_127 assump_193
                exact assump_184
  let assump_75 := assump_72 assump_191
  let assump_186 := And.left assump_75
  have assump_194 : ((p1 ∧ p1) ∨ (True ∨ p3)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_187 := assump_186 assump_194
  apply False.elim assump_187


variable (p0 p1 p6 p5 p7 p4 : Prop)
theorem file52_144548 : (((((p5 → False) → False) ∧ ((False → p4) ∧ (False ∧ p0))) → False) ∨ ((((p0 → False) ∨ (True ∧ True)) ∨ ((p1 ∨ p7) ∨ (p5 → False))) ∨ (((False ∨ p6) ∨ (p4 ∨ p7)) ∨ ((p5 → p1) ∧ (p0 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10


variable (p3 p4 p7 p0 p2 : Prop)
theorem file52_145037 : ((((((p0 ∧ p0) → (p2 ∨ True)) → False) → (((p2 → False) ∧ (p7 ∧ p2)) → ((p4 → p2) ∧ (p3 ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p0 ∧ p0) → (p2 ∨ True)) → False) → (((p2 → False) ∧ (p7 ∧ p2)) → ((p4 → p2) ∧ (p3 ∨ p7)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        exact assump_15
    cases assump_6
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        apply Or.inr
        exact assump_26
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p1 p7 p2 p4 p5 p6 p0 p3 : Prop)
theorem file52_145810 : (((((p2 ∧ p6) ∨ (p5 ∧ p4)) ∧ ((p1 → False) ∧ (p2 ∧ p3))) → (((False → False) → (p5 ∧ p3)) ∨ ((p7 ∧ p3) → (True → False)))) → ((((p4 → False) → (p4 → p0)) ∧ ((True ∨ p7) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_16 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_12 := assump_4 assump_16
    apply False.elim assump_12


variable (p0 p2 p1 p7 p3 p5 p4 p6 : Prop)
theorem file52_146308 : ((((((True ∨ p1) ∧ (p5 → p0)) → ((p2 → True) ∨ (p1 ∨ p1))) → (((p0 ∨ True) ∧ (p1 → False)) → ((p1 → True) ∨ (True ∧ p1)))) ∧ ((((p4 ∨ p6) ∧ (p7 ∧ False)) ∨ ((p0 ∨ p3) ∨ (p7 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p4 ∨ p6) ∧ (p7 ∧ False)) ∨ ((p0 ∨ p3) ∨ (p7 → p7))) := by
      apply Or.inr
      apply Or.inr
      intro assump_9
      exact assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p1 p0 p7 p3 p6 p4 p5 : Prop)
theorem file52_146876 : ((((((p5 → p0) ∨ (True → p6)) → ((p5 ∨ True) ∧ (p0 ∧ p4))) → (((p3 → p1) ∧ (False ∧ p4)) → ((p1 → False) ∨ (p7 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 → p0) ∨ (True → p6)) → ((p5 ∨ True) ∧ (p0 ∧ p4))) → (((p3 → p1) ∧ (False ∧ p4)) → ((p1 → False) ∨ (p7 ∨ p0)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p1 p0 p3 p5 p6 p4 p2 : Prop)
theorem file52_147500 : ((((((False ∨ p3) ∧ (p7 ∧ False)) ∨ ((p7 → False) → (p5 ∨ p6))) → (((p1 → p5) → (p7 → p3)) ∧ ((True → p2) → False))) ∧ ((((p0 ∨ p5) → False) → ((p3 → p7) ∨ (p2 → p7))) ∧ (((p4 ∨ True) → False) ∧ ((p7 → False) ∨ (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          have assump_30 : (p4 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_19 := assump_10 assump_30
          apply False.elim assump_19
        case inr assump_15 =>
          have assump_31 : (p4 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_26 := assump_10 assump_31
          apply False.elim assump_26


variable (p5 p3 p0 p2 p7 p6 : Prop)
theorem file52_148437 : (((((False ∧ p6) ∧ (p3 ∧ p0)) → ((p2 → p5) ∨ (p5 → p7))) → False) → False) := by
  intro assump_1
  have assump_15 : (((False ∧ p6) ∧ (p3 ∧ p0)) → ((p2 → p5) ∨ (p5 → p7))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p2 p6 p5 p1 p0 p4 p3 : Prop)
theorem file52_148913 : (((((p3 ∨ False) ∧ (False → False)) → ((p7 → False) ∨ (p7 → False))) ∨ (((True ∨ p6) ∧ (p5 ∧ p4)) ∧ ((p4 → p5) → (False ∧ p0)))) → ((((True ∧ p2) ∧ (False → False)) ∧ ((True → False) ∧ (p4 → p3))) → (((p1 ∨ p0) ∨ (p6 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_11
            case intro assump_22 assump_23 =>
              cases assump_1
              case inl assump_28 =>
                have assump_224 : True := by
                  apply True.intro
                let assump_34 := assump_22 assump_224
                apply False.elim assump_34
              case inr assump_29 =>
                cases assump_29
                case intro assump_38 assump_39 =>
                  cases assump_38
                  case intro assump_40 assump_41 =>
                    cases assump_40
                    case inl assump_42 =>
                      cases assump_41
                      case intro assump_46 assump_47 =>
                        have assump_225 : (p4 → p5) := by
                          intro assump_55
                          exact assump_46
                        let assump_54 := assump_39 assump_225
                        let assump_58 := And.left assump_54
                        apply False.elim assump_58
                    case inr assump_43 =>
                      cases assump_41
                      case intro assump_64 assump_65 =>
                        have assump_226 : (p4 → p5) := by
                          intro assump_73
                          exact assump_64
                        let assump_72 := assump_39 assump_226
                        let assump_76 := And.left assump_72
                        apply False.elim assump_76
    case inr assump_7 =>
      cases assump_2
      case intro assump_82 assump_83 =>
        cases assump_82
        case intro assump_84 assump_85 =>
          cases assump_84
          case intro assump_86 assump_87 =>
            cases assump_83
            case intro assump_94 assump_95 =>
              cases assump_1
              case inl assump_100 =>
                have assump_227 : True := by
                  apply True.intro
                let assump_106 := assump_94 assump_227
                apply False.elim assump_106
              case inr assump_101 =>
                cases assump_101
                case intro assump_110 assump_111 =>
                  cases assump_110
                  case intro assump_112 assump_113 =>
                    cases assump_112
                    case inl assump_114 =>
                      cases assump_113
                      case intro assump_118 assump_119 =>
                        have assump_228 : (p4 → p5) := by
                          intro assump_127
                          exact assump_118
                        let assump_126 := assump_111 assump_228
                        let assump_130 := And.left assump_126
                        apply False.elim assump_130
                    case inr assump_115 =>
                      cases assump_113
                      case intro assump_136 assump_137 =>
                        have assump_229 : (p4 → p5) := by
                          intro assump_145
                          exact assump_136
                        let assump_144 := assump_111 assump_229
                        let assump_148 := And.left assump_144
                        apply False.elim assump_148
  case inr assump_5 =>
    cases assump_2
    case intro assump_154 assump_155 =>
      cases assump_154
      case intro assump_156 assump_157 =>
        cases assump_156
        case intro assump_158 assump_159 =>
          cases assump_155
          case intro assump_166 assump_167 =>
            cases assump_1
            case inl assump_172 =>
              have assump_230 : True := by
                apply True.intro
              let assump_178 := assump_166 assump_230
              apply False.elim assump_178
            case inr assump_173 =>
              cases assump_173
              case intro assump_182 assump_183 =>
                cases assump_182
                case intro assump_184 assump_185 =>
                  cases assump_184
                  case inl assump_186 =>
                    cases assump_185
                    case intro assump_190 assump_191 =>
                      have assump_231 : (p4 → p5) := by
                        intro assump_199
                        exact assump_190
                      let assump_198 := assump_183 assump_231
                      let assump_202 := And.left assump_198
                      apply False.elim assump_202
                  case inr assump_187 =>
                    cases assump_185
                    case intro assump_208 assump_209 =>
                      have assump_232 : (p4 → p5) := by
                        intro assump_217
                        exact assump_208
                      let assump_216 := assump_183 assump_232
                      let assump_220 := And.left assump_216
                      apply False.elim assump_220


variable (p7 p4 p3 p0 p5 p2 : Prop)
theorem file52_154367 : ((((((False → p3) → (False → False)) ∨ ((p7 ∨ True) → False)) ∨ (((p0 ∧ p5) ∨ (p2 ∨ p4)) → ((False → p2) → False))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((False → p3) → (False → False)) ∨ ((p7 ∨ True) → False)) ∨ (((p0 ∧ p5) ∨ (p2 ∨ p4)) → ((False → p2) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p4 p6 p5 p1 : Prop)
theorem file52_154887 : (((((False ∧ p4) → (p5 ∧ False)) ∨ ((p4 → p1) ∨ (p5 → p1))) ∧ (((False → False) → False) → False)) ∨ ((((False → True) ∨ (p5 → p5)) ∨ ((False ∨ p4) → (p6 ∧ p0))) ∧ (((p6 ∧ False) ∧ (p0 → p0)) → False))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2
  cases assump_1
  case intro assump_6 assump_7 =>
    apply False.elim assump_6
  intro assump_10
  have assump_20 : (False → False) := by
    intro assump_14
    apply False.elim assump_14
  let assump_13 := assump_10 assump_20
  apply False.elim assump_13


variable (p0 p6 p2 p3 p1 : Prop)
theorem file52_155576 : (((((p6 ∧ False) → False) → False) ∧ (((p1 → p0) ∨ (p6 → False)) ∧ ((True → p1) ∧ (True ∧ p6)))) → ((((False → False) ∨ (p1 ∨ p0)) → False) ∨ (((p2 → False) ∨ (p3 ∧ True)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            apply Or.inl
            intro assump_22
            cases assump_22
            case inl assump_23 =>
              have assump_129 : ((p6 ∧ False) → False) := by
                intro assump_33
                cases assump_33
                case intro assump_34 assump_35 =>
                  apply False.elim assump_35
              let assump_32 := assump_2 assump_129
              apply False.elim assump_32
            case inr assump_24 =>
              cases assump_24
              case inl assump_43 =>
                have assump_130 : ((p6 ∧ False) → False) := by
                  intro assump_54
                  cases assump_54
                  case intro assump_55 assump_56 =>
                    apply False.elim assump_56
                let assump_53 := assump_2 assump_130
                apply False.elim assump_53
              case inr assump_44 =>
                have assump_131 : ((p6 ∧ False) → False) := by
                  intro assump_72
                  cases assump_72
                  case intro assump_73 assump_74 =>
                    apply False.elim assump_74
                let assump_71 := assump_2 assump_131
                apply False.elim assump_71
      case inr assump_9 =>
        cases assump_7
        case intro assump_84 assump_85 =>
          cases assump_85
          case intro assump_88 assump_89 =>
            apply Or.inl
            intro assump_94
            cases assump_94
            case inl assump_95 =>
              have assump_132 : p6 := by
                exact assump_89
              let assump_103 := assump_9 assump_132
              apply False.elim assump_103
            case inr assump_96 =>
              cases assump_96
              case inl assump_107 =>
                have assump_133 : p6 := by
                  exact assump_89
                let assump_115 := assump_9 assump_133
                apply False.elim assump_115
              case inr assump_108 =>
                have assump_134 : p6 := by
                  exact assump_89
                let assump_125 := assump_9 assump_134
                apply False.elim assump_125


variable (p6 p7 p5 p3 p1 p4 p0 : Prop)
theorem file52_158281 : (((((p3 → False) → (p4 → False)) → False) ∧ (((p6 ∨ False) → False) ∧ ((True ∧ p3) ∧ (p6 ∧ p0)))) → ((((False → False) → False) ∨ ((p7 → p7) ∨ (True ∨ p1))) ∨ (((p1 → p6) ∨ (p6 ∨ True)) ∧ ((p5 ∨ p0) ∨ (p4 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply Or.inl
            apply Or.inl
            intro assump_24
            have assump_35 : (p6 ∨ False) := by
              apply Or.inl
              exact assump_18
            let assump_31 := assump_6 assump_35
            apply False.elim assump_31


variable (p1 p3 p7 p4 p5 p2 p6 p0 : Prop)
theorem file52_159161 : ((((((p4 → p4) → False) → ((False ∨ p3) → False)) → False) ∨ ((((p2 ∧ p2) ∧ (p1 → False)) ∧ ((p5 ∧ p6) ∧ (p0 → False))) ∧ (((p3 ∧ p6) → (True ∨ p7)) → ((p1 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_66 : (((p4 → p4) → False) → ((False ∨ p3) → False)) := by
      intro assump_7
      intro assump_8
      cases assump_8
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        have assump_67 : (p4 → p4) := by
          intro assump_18
          exact assump_18
        let assump_17 := assump_7 assump_67
        apply False.elim assump_17
    let assump_6 := assump_2 assump_66
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            cases assump_30
            case intro assump_41 assump_42 =>
              cases assump_41
              case intro assump_43 assump_44 =>
                have assump_68 : ((p3 ∧ p6) → (True ∨ p7)) := by
                  intro assump_54
                  cases assump_54
                  case intro assump_55 assump_56 =>
                    apply Or.inl
                    apply True.intro
                let assump_53 := assump_28 assump_68
                have assump_69 : (p1 → True) := by
                  intro assump_62
                  apply True.intro
                let assump_61 := assump_53 assump_69
                apply False.elim assump_61


variable (p5 p7 p3 p0 p1 p2 p6 p4 : Prop)
theorem file52_160896 : (((((True → p5) → (p3 → p4)) ∧ ((p1 ∨ p1) ∧ (p5 → p6))) ∨ (((p6 → False) ∧ (p5 ∨ p0)) → False)) → ((((p5 → p7) → (p1 → False)) → False) → (((p1 ∧ p1) ∨ (True ∧ True)) ∨ ((p1 → True) ∧ (p2 ∨ p6))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          apply Or.inl
          apply And.intro
          exact assump_13
          exact assump_13
        case inr assump_14 =>
          apply Or.inl
          apply Or.inl
          apply And.intro
          exact assump_14
          exact assump_14
  case inr assump_6 =>
    apply Or.inl
    apply Or.inr
    apply And.intro
    apply True.intro
    apply True.intro


variable (p3 p5 p2 p1 p6 p4 p0 : Prop)
theorem file52_161804 : ((((((p4 ∨ True) → False) → False) ∧ (((False ∧ p3) → False) → False)) ∧ ((((p0 → p1) ∨ (p5 → p3)) ∨ ((p5 → p3) ∧ (p4 ∨ p4))) ∧ (((p4 ∨ False) ∨ (p2 ∨ p1)) ∧ ((p5 → False) ∨ (p6 → p1))))) → False) := by
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
          case inl assump_14 =>
            cases assump_11
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_20
                case inl assump_22 =>
                  cases assump_19
                  case inl assump_26 =>
                    have assump_466 : ((False ∧ p3) → False) := by
                      intro assump_34
                      cases assump_34
                      case intro assump_35 assump_36 =>
                        apply False.elim assump_35
                    let assump_33 := assump_5 assump_466
                    apply False.elim assump_33
                  case inr assump_27 =>
                    have assump_467 : ((False ∧ p3) → False) := by
                      intro assump_48
                      cases assump_48
                      case intro assump_49 assump_50 =>
                        apply False.elim assump_49
                    let assump_47 := assump_5 assump_467
                    apply False.elim assump_47
                case inr assump_23 =>
                  apply False.elim assump_23
              case inr assump_21 =>
                cases assump_21
                case inl assump_58 =>
                  cases assump_19
                  case inl assump_62 =>
                    have assump_468 : ((False ∧ p3) → False) := by
                      intro assump_70
                      cases assump_70
                      case intro assump_71 assump_72 =>
                        apply False.elim assump_71
                    let assump_69 := assump_5 assump_468
                    apply False.elim assump_69
                  case inr assump_63 =>
                    have assump_469 : ((False ∧ p3) → False) := by
                      intro assump_84
                      cases assump_84
                      case intro assump_85 assump_86 =>
                        apply False.elim assump_85
                    let assump_83 := assump_5 assump_469
                    apply False.elim assump_83
                case inr assump_59 =>
                  cases assump_19
                  case inl assump_94 =>
                    have assump_470 : ((False ∧ p3) → False) := by
                      intro assump_102
                      cases assump_102
                      case intro assump_103 assump_104 =>
                        apply False.elim assump_103
                    let assump_101 := assump_5 assump_470
                    apply False.elim assump_101
                  case inr assump_95 =>
                    have assump_471 : ((False ∧ p3) → False) := by
                      intro assump_116
                      cases assump_116
                      case intro assump_117 assump_118 =>
                        apply False.elim assump_117
                    let assump_115 := assump_5 assump_471
                    apply False.elim assump_115
          case inr assump_15 =>
            cases assump_11
            case intro assump_126 assump_127 =>
              cases assump_126
              case inl assump_128 =>
                cases assump_128
                case inl assump_130 =>
                  cases assump_127
                  case inl assump_134 =>
                    have assump_472 : ((False ∧ p3) → False) := by
                      intro assump_142
                      cases assump_142
                      case intro assump_143 assump_144 =>
                        apply False.elim assump_143
                    let assump_141 := assump_5 assump_472
                    apply False.elim assump_141
                  case inr assump_135 =>
                    have assump_473 : ((False ∧ p3) → False) := by
                      intro assump_156
                      cases assump_156
                      case intro assump_157 assump_158 =>
                        apply False.elim assump_157
                    let assump_155 := assump_5 assump_473
                    apply False.elim assump_155
                case inr assump_131 =>
                  apply False.elim assump_131
              case inr assump_129 =>
                cases assump_129
                case inl assump_166 =>
                  cases assump_127
                  case inl assump_170 =>
                    have assump_474 : ((False ∧ p3) → False) := by
                      intro assump_178
                      cases assump_178
                      case intro assump_179 assump_180 =>
                        apply False.elim assump_179
                    let assump_177 := assump_5 assump_474
                    apply False.elim assump_177
                  case inr assump_171 =>
                    have assump_475 : ((False ∧ p3) → False) := by
                      intro assump_192
                      cases assump_192
                      case intro assump_193 assump_194 =>
                        apply False.elim assump_193
                    let assump_191 := assump_5 assump_475
                    apply False.elim assump_191
                case inr assump_167 =>
                  cases assump_127
                  case inl assump_202 =>
                    have assump_476 : ((False ∧ p3) → False) := by
                      intro assump_210
                      cases assump_210
                      case intro assump_211 assump_212 =>
                        apply False.elim assump_211
                    let assump_209 := assump_5 assump_476
                    apply False.elim assump_209
                  case inr assump_203 =>
                    have assump_477 : ((False ∧ p3) → False) := by
                      intro assump_224
                      cases assump_224
                      case intro assump_225 assump_226 =>
                        apply False.elim assump_225
                    let assump_223 := assump_5 assump_477
                    apply False.elim assump_223
        case inr assump_13 =>
          cases assump_13
          case intro assump_232 assump_233 =>
            cases assump_233
            case inl assump_236 =>
              cases assump_11
              case intro assump_240 assump_241 =>
                cases assump_240
                case inl assump_242 =>
                  cases assump_242
                  case inl assump_244 =>
                    cases assump_241
                    case inl assump_248 =>
                      have assump_478 : ((False ∧ p3) → False) := by
                        intro assump_257
                        cases assump_257
                        case intro assump_258 assump_259 =>
                          apply False.elim assump_258
                      let assump_256 := assump_5 assump_478
                      apply False.elim assump_256
                    case inr assump_249 =>
                      have assump_479 : ((False ∧ p3) → False) := by
                        intro assump_272
                        cases assump_272
                        case intro assump_273 assump_274 =>
                          apply False.elim assump_273
                      let assump_271 := assump_5 assump_479
                      apply False.elim assump_271
                  case inr assump_245 =>
                    apply False.elim assump_245
                case inr assump_243 =>
                  cases assump_243
                  case inl assump_282 =>
                    cases assump_241
                    case inl assump_286 =>
                      have assump_480 : ((False ∧ p3) → False) := by
                        intro assump_295
                        cases assump_295
                        case intro assump_296 assump_297 =>
                          apply False.elim assump_296
                      let assump_294 := assump_5 assump_480
                      apply False.elim assump_294
                    case inr assump_287 =>
                      have assump_481 : ((False ∧ p3) → False) := by
                        intro assump_310
                        cases assump_310
                        case intro assump_311 assump_312 =>
                          apply False.elim assump_311
                      let assump_309 := assump_5 assump_481
                      apply False.elim assump_309
                  case inr assump_283 =>
                    cases assump_241
                    case inl assump_320 =>
                      have assump_482 : ((False ∧ p3) → False) := by
                        intro assump_329
                        cases assump_329
                        case intro assump_330 assump_331 =>
                          apply False.elim assump_330
                      let assump_328 := assump_5 assump_482
                      apply False.elim assump_328
                    case inr assump_321 =>
                      have assump_483 : ((False ∧ p3) → False) := by
                        intro assump_344
                        cases assump_344
                        case intro assump_345 assump_346 =>
                          apply False.elim assump_345
                      let assump_343 := assump_5 assump_483
                      apply False.elim assump_343
            case inr assump_237 =>
              cases assump_11
              case intro assump_354 assump_355 =>
                cases assump_354
                case inl assump_356 =>
                  cases assump_356
                  case inl assump_358 =>
                    cases assump_355
                    case inl assump_362 =>
                      have assump_484 : ((False ∧ p3) → False) := by
                        intro assump_371
                        cases assump_371
                        case intro assump_372 assump_373 =>
                          apply False.elim assump_372
                      let assump_370 := assump_5 assump_484
                      apply False.elim assump_370
                    case inr assump_363 =>
                      have assump_485 : ((False ∧ p3) → False) := by
                        intro assump_386
                        cases assump_386
                        case intro assump_387 assump_388 =>
                          apply False.elim assump_387
                      let assump_385 := assump_5 assump_485
                      apply False.elim assump_385
                  case inr assump_359 =>
                    apply False.elim assump_359
                case inr assump_357 =>
                  cases assump_357
                  case inl assump_396 =>
                    cases assump_355
                    case inl assump_400 =>
                      have assump_486 : ((False ∧ p3) → False) := by
                        intro assump_409
                        cases assump_409
                        case intro assump_410 assump_411 =>
                          apply False.elim assump_410
                      let assump_408 := assump_5 assump_486
                      apply False.elim assump_408
                    case inr assump_401 =>
                      have assump_487 : ((False ∧ p3) → False) := by
                        intro assump_424
                        cases assump_424
                        case intro assump_425 assump_426 =>
                          apply False.elim assump_425
                      let assump_423 := assump_5 assump_487
                      apply False.elim assump_423
                  case inr assump_397 =>
                    cases assump_355
                    case inl assump_434 =>
                      have assump_488 : ((False ∧ p3) → False) := by
                        intro assump_443
                        cases assump_443
                        case intro assump_444 assump_445 =>
                          apply False.elim assump_444
                      let assump_442 := assump_5 assump_488
                      apply False.elim assump_442
                    case inr assump_435 =>
                      have assump_489 : ((False ∧ p3) → False) := by
                        intro assump_458
                        cases assump_458
                        case intro assump_459 assump_460 =>
                          apply False.elim assump_459
                      let assump_457 := assump_5 assump_489
                      apply False.elim assump_457


variable (p4 p2 p0 p5 p6 : Prop)
theorem file52_174660 : (((((p2 → False) ∧ (True ∧ False)) → ((p4 → False) ∧ (p6 → True))) ∧ (((True → False) ∧ (p0 ∧ True)) ∨ ((True → False) ∧ (False ∨ p5)))) → False) := by
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    cases assump_23
    case inl assump_26 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_29
        case intro assump_32 assump_33 =>
          have assump_58 : True := by
            apply True.intro
          let assump_39 := assump_28 assump_58
          apply False.elim assump_39
    case inr assump_27 =>
      cases assump_27
      case intro assump_43 assump_44 =>
        cases assump_44
        case inl assump_47 =>
          apply False.elim assump_47
        case inr assump_48 =>
          have assump_59 : True := by
            apply True.intro
          let assump_54 := assump_43 assump_59
          apply False.elim assump_54


