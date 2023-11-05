variable (p2 p0 p7 p3 p4 : Prop)
theorem file62_41 : (((((p0 → p0) → False) ∧ ((True ∨ p4) → False)) ∧ (((p2 ∨ p3) ∧ (False ∨ p4)) ∧ ((p2 → p2) ∧ (p7 ∨ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case inl assump_18 =>
              apply False.elim assump_18
            case inr assump_19 =>
              cases assump_11
              case intro assump_24 assump_25 =>
                cases assump_25
                case inl assump_28 =>
                  have assump_86 : (True ∨ p4) := by
                    apply Or.inl
                    apply True.intro
                  let assump_37 := assump_5 assump_86
                  apply False.elim assump_37
                case inr assump_29 =>
                  have assump_87 : (True ∨ p4) := by
                    apply Or.inl
                    apply True.intro
                  let assump_48 := assump_5 assump_87
                  apply False.elim assump_48
          case inr assump_15 =>
            cases assump_13
            case inl assump_54 =>
              apply False.elim assump_54
            case inr assump_55 =>
              cases assump_11
              case intro assump_60 assump_61 =>
                cases assump_61
                case inl assump_64 =>
                  have assump_88 : (True ∨ p4) := by
                    apply Or.inl
                    apply True.intro
                  let assump_72 := assump_5 assump_88
                  apply False.elim assump_72
                case inr assump_65 =>
                  have assump_89 : (True ∨ p4) := by
                    apply Or.inl
                    apply True.intro
                  let assump_82 := assump_5 assump_89
                  apply False.elim assump_82


variable (p6 p2 p0 p5 p4 p3 p1 p7 : Prop)
theorem file62_2102 : ((((((True ∨ p6) → (p2 ∧ p5)) ∧ ((p6 ∨ p4) ∧ (p2 → False))) ∧ (((p2 → False) ∨ (p3 ∨ p0)) → ((p6 → False) → False))) ∧ ((((True ∧ p3) ∧ (p4 → False)) ∧ ((p3 → False) ∧ (p5 → p5))) ∧ (((p6 ∨ p1) ∨ (p3 → p7)) ∨ ((p1 ∨ p7) ∧ (p2 ∧ p0))))) → False) := by
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
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    cases assump_23
                    case intro assump_34 assump_35 =>
                      cases assump_21
                      case inl assump_40 =>
                        cases assump_40
                        case inl assump_42 =>
                          cases assump_42
                          case inl assump_44 =>
                            have assump_200 : p3 := by
                              exact assump_27
                            let assump_50 := assump_34 assump_200
                            apply False.elim assump_50
                          case inr assump_45 =>
                            have assump_201 : p3 := by
                              exact assump_27
                            let assump_58 := assump_34 assump_201
                            apply False.elim assump_58
                        case inr assump_43 =>
                          have assump_202 : p3 := by
                            exact assump_27
                          let assump_67 := assump_34 assump_202
                          apply False.elim assump_67
                      case inr assump_41 =>
                        cases assump_41
                        case intro assump_71 assump_72 =>
                          cases assump_71
                          case inl assump_73 =>
                            cases assump_72
                            case intro assump_77 assump_78 =>
                              have assump_203 : p3 := by
                                exact assump_27
                              let assump_87 := assump_34 assump_203
                              apply False.elim assump_87
                          case inr assump_74 =>
                            cases assump_72
                            case intro assump_93 assump_94 =>
                              have assump_204 : p3 := by
                                exact assump_27
                              let assump_103 := assump_34 assump_204
                              apply False.elim assump_103
          case inr assump_13 =>
            cases assump_3
            case intro assump_113 assump_114 =>
              cases assump_113
              case intro assump_115 assump_116 =>
                cases assump_115
                case intro assump_117 assump_118 =>
                  cases assump_117
                  case intro assump_119 assump_120 =>
                    cases assump_116
                    case intro assump_127 assump_128 =>
                      cases assump_114
                      case inl assump_133 =>
                        cases assump_133
                        case inl assump_135 =>
                          cases assump_135
                          case inl assump_137 =>
                            have assump_205 : p3 := by
                              exact assump_120
                            let assump_143 := assump_127 assump_205
                            apply False.elim assump_143
                          case inr assump_138 =>
                            have assump_206 : p3 := by
                              exact assump_120
                            let assump_151 := assump_127 assump_206
                            apply False.elim assump_151
                        case inr assump_136 =>
                          have assump_207 : p3 := by
                            exact assump_120
                          let assump_160 := assump_127 assump_207
                          apply False.elim assump_160
                      case inr assump_134 =>
                        cases assump_134
                        case intro assump_164 assump_165 =>
                          cases assump_164
                          case inl assump_166 =>
                            cases assump_165
                            case intro assump_170 assump_171 =>
                              have assump_208 : p3 := by
                                exact assump_120
                              let assump_180 := assump_127 assump_208
                              apply False.elim assump_180
                          case inr assump_167 =>
                            cases assump_165
                            case intro assump_186 assump_187 =>
                              have assump_209 : p3 := by
                                exact assump_120
                              let assump_196 := assump_127 assump_209
                              apply False.elim assump_196


variable (p0 p6 p5 p4 p7 p3 p2 : Prop)
theorem file62_7552 : ((((((p0 → p3) → (p2 → False)) ∨ ((p3 ∧ p6) ∨ (p7 ∧ p7))) ∧ (((p4 → False) ∧ (p6 ∧ p4)) → False)) ∧ ((((p3 → False) ∧ (p0 ∨ p4)) ∧ ((p7 ∧ False) → (False → p4))) ∧ (((p3 ∨ p3) ∧ (False ∧ False)) ∧ ((p2 → False) ∧ (p5 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_17
              case inl assump_20 =>
                cases assump_13
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_29
                      case intro assump_34 assump_35 =>
                        apply False.elim assump_34
                    case inr assump_31 =>
                      cases assump_29
                      case intro assump_40 assump_41 =>
                        apply False.elim assump_40
              case inr assump_21 =>
                cases assump_13
                case intro assump_48 assump_49 =>
                  cases assump_48
                  case intro assump_50 assump_51 =>
                    cases assump_50
                    case inl assump_52 =>
                      cases assump_51
                      case intro assump_56 assump_57 =>
                        apply False.elim assump_56
                    case inr assump_53 =>
                      cases assump_51
                      case intro assump_62 assump_63 =>
                        apply False.elim assump_62
      case inr assump_7 =>
        cases assump_7
        case inl assump_66 =>
          cases assump_66
          case intro assump_68 assump_69 =>
            cases assump_3
            case intro assump_76 assump_77 =>
              cases assump_76
              case intro assump_78 assump_79 =>
                cases assump_78
                case intro assump_80 assump_81 =>
                  cases assump_81
                  case inl assump_84 =>
                    cases assump_77
                    case intro assump_90 assump_91 =>
                      cases assump_90
                      case intro assump_92 assump_93 =>
                        cases assump_92
                        case inl assump_94 =>
                          cases assump_93
                          case intro assump_98 assump_99 =>
                            apply False.elim assump_98
                        case inr assump_95 =>
                          cases assump_93
                          case intro assump_104 assump_105 =>
                            apply False.elim assump_104
                  case inr assump_85 =>
                    cases assump_77
                    case intro assump_112 assump_113 =>
                      cases assump_112
                      case intro assump_114 assump_115 =>
                        cases assump_114
                        case inl assump_116 =>
                          cases assump_115
                          case intro assump_120 assump_121 =>
                            apply False.elim assump_120
                        case inr assump_117 =>
                          cases assump_115
                          case intro assump_126 assump_127 =>
                            apply False.elim assump_126
        case inr assump_67 =>
          cases assump_67
          case intro assump_130 assump_131 =>
            cases assump_3
            case intro assump_138 assump_139 =>
              cases assump_138
              case intro assump_140 assump_141 =>
                cases assump_140
                case intro assump_142 assump_143 =>
                  cases assump_143
                  case inl assump_146 =>
                    cases assump_139
                    case intro assump_152 assump_153 =>
                      cases assump_152
                      case intro assump_154 assump_155 =>
                        cases assump_154
                        case inl assump_156 =>
                          cases assump_155
                          case intro assump_160 assump_161 =>
                            apply False.elim assump_160
                        case inr assump_157 =>
                          cases assump_155
                          case intro assump_166 assump_167 =>
                            apply False.elim assump_166
                  case inr assump_147 =>
                    cases assump_139
                    case intro assump_174 assump_175 =>
                      cases assump_174
                      case intro assump_176 assump_177 =>
                        cases assump_176
                        case inl assump_178 =>
                          cases assump_177
                          case intro assump_182 assump_183 =>
                            apply False.elim assump_182
                        case inr assump_179 =>
                          cases assump_177
                          case intro assump_188 assump_189 =>
                            apply False.elim assump_188


variable (p7 p1 p3 p6 p4 p0 p5 : Prop)
theorem file62_13028 : (((((p3 ∧ p1) → (False → False)) → False) → (((p4 ∨ p4) ∨ (p0 ∨ p7)) → ((p4 ∧ p3) → (p5 ∧ p1)))) ∨ ((((p5 ∧ p4) → (True ∨ p0)) ∨ ((False → False) ∧ (p6 ∨ False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case inl assump_10 =>
      cases assump_10
      case inl assump_12 =>
        have assump_124 : ((p3 ∧ p1) → (False → False)) := by
          intro assump_19
          intro assump_20
          apply False.elim assump_20
        let assump_18 := assump_1 assump_124
        apply False.elim assump_18
      case inr assump_13 =>
        have assump_125 : ((p3 ∧ p1) → (False → False)) := by
          intro assump_31
          intro assump_32
          apply False.elim assump_32
        let assump_30 := assump_1 assump_125
        apply False.elim assump_30
    case inr assump_11 =>
      cases assump_11
      case inl assump_38 =>
        have assump_126 : ((p3 ∧ p1) → (False → False)) := by
          intro assump_45
          intro assump_46
          apply False.elim assump_46
        let assump_44 := assump_1 assump_126
        apply False.elim assump_44
      case inr assump_39 =>
        have assump_127 : ((p3 ∧ p1) → (False → False)) := by
          intro assump_57
          intro assump_58
          apply False.elim assump_58
        let assump_56 := assump_1 assump_127
        apply False.elim assump_56
  cases assump_3
  case intro assump_64 assump_65 =>
    cases assump_2
    case inl assump_70 =>
      cases assump_70
      case inl assump_72 =>
        have assump_128 : ((p3 ∧ p1) → (False → False)) := by
          intro assump_79
          intro assump_80
          apply False.elim assump_80
        let assump_78 := assump_1 assump_128
        apply False.elim assump_78
      case inr assump_73 =>
        have assump_129 : ((p3 ∧ p1) → (False → False)) := by
          intro assump_91
          intro assump_92
          apply False.elim assump_92
        let assump_90 := assump_1 assump_129
        apply False.elim assump_90
    case inr assump_71 =>
      cases assump_71
      case inl assump_98 =>
        have assump_130 : ((p3 ∧ p1) → (False → False)) := by
          intro assump_105
          intro assump_106
          apply False.elim assump_106
        let assump_104 := assump_1 assump_130
        apply False.elim assump_104
      case inr assump_99 =>
        have assump_131 : ((p3 ∧ p1) → (False → False)) := by
          intro assump_117
          intro assump_118
          apply False.elim assump_118
        let assump_116 := assump_1 assump_131
        apply False.elim assump_116


variable (p1 p3 p6 p4 p0 : Prop)
theorem file62_15764 : ((((((p1 ∨ p0) ∨ (p3 ∧ p4)) ∧ ((p4 → False) → False)) → (((p3 → False) ∨ (p6 → p6)) → ((p1 → p1) ∧ (p3 → p3)))) → False) → False) := by
  intro assump_1
  have assump_116 : ((((p1 ∨ p0) ∨ (p3 ∧ p4)) ∧ ((p4 → False) → False)) → (((p3 → False) ∨ (p6 → p6)) → ((p1 → p1) ∧ (p3 → p3)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case inl assump_18 =>
            exact assump_18
          case inr assump_19 =>
            exact assump_7
        case inr assump_17 =>
          cases assump_17
          case intro assump_28 assump_29 =>
            exact assump_7
    case inr assump_11 =>
      cases assump_5
      case intro assump_38 assump_39 =>
        cases assump_38
        case inl assump_40 =>
          cases assump_40
          case inl assump_42 =>
            exact assump_42
          case inr assump_43 =>
            exact assump_7
        case inr assump_41 =>
          cases assump_41
          case intro assump_52 assump_53 =>
            exact assump_7
    intro assump_60
    cases assump_6
    case inl assump_63 =>
      cases assump_5
      case intro assump_67 assump_68 =>
        cases assump_67
        case inl assump_69 =>
          cases assump_69
          case inl assump_71 =>
            exact assump_60
          case inr assump_72 =>
            exact assump_60
        case inr assump_70 =>
          cases assump_70
          case intro assump_81 assump_82 =>
            exact assump_81
    case inr assump_64 =>
      cases assump_5
      case intro assump_91 assump_92 =>
        cases assump_91
        case inl assump_93 =>
          cases assump_93
          case inl assump_95 =>
            exact assump_60
          case inr assump_96 =>
            exact assump_60
        case inr assump_94 =>
          cases assump_94
          case intro assump_105 assump_106 =>
            exact assump_105
  let assump_4 := assump_1 assump_116
  apply False.elim assump_4


variable (p6 p2 p7 p1 p5 p4 p3 : Prop)
theorem file62_17976 : (((((p3 ∧ p3) ∧ (p6 → False)) → False) → False) → ((((p7 ∧ p2) ∨ (p3 → False)) ∧ ((p7 ∧ p3) ∧ (p4 ∧ p1))) → (((p6 → False) ∧ (p7 ∧ p7)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_14
            case intro assump_21 assump_22 =>
              apply Or.inl
              apply And.intro
              intro assump_29
              have assump_93 : (((p3 ∧ p3) ∧ (p6 → False)) → False) := by
                intro assump_34
                cases assump_34
                case intro assump_35 assump_36 =>
                  cases assump_35
                  case intro assump_37 assump_38 =>
                    have assump_94 : p6 := by
                      exact assump_29
                    let assump_45 := assump_36 assump_94
                    apply False.elim assump_45
              let assump_33 := assump_1 assump_93
              apply False.elim assump_33
              apply And.intro
              exact assump_15
              exact assump_15
    case inr assump_6 =>
      cases assump_4
      case intro assump_54 assump_55 =>
        cases assump_54
        case intro assump_56 assump_57 =>
          cases assump_55
          case intro assump_62 assump_63 =>
            apply Or.inl
            apply And.intro
            intro assump_70
            have assump_95 : (((p3 ∧ p3) ∧ (p6 → False)) → False) := by
              intro assump_75
              cases assump_75
              case intro assump_76 assump_77 =>
                cases assump_76
                case intro assump_78 assump_79 =>
                  have assump_96 : p6 := by
                    exact assump_70
                  let assump_86 := assump_77 assump_96
                  apply False.elim assump_86
            let assump_74 := assump_1 assump_95
            apply False.elim assump_74
            apply And.intro
            exact assump_56
            exact assump_56


variable (p3 p1 p6 p7 p5 p2 p0 : Prop)
theorem file62_20252 : (((((p0 → False) ∧ (p1 ∨ p6)) → ((False ∧ p1) → False)) ∨ (((p5 ∨ False) ∧ (p3 ∨ p0)) ∨ ((p2 ∨ p7) ∧ (False ∨ False)))) → ((((p2 ∨ True) ∨ (p6 ∨ True)) → ((True ∧ p5) ∨ (p2 ∨ True))) ∨ (((p3 → False) ∨ (p2 ∨ p0)) ∧ ((True ∨ True) ∧ (p1 → False))))) := by
  intro assump_26
  cases assump_26
  case inl assump_27 =>
    apply Or.inl
    intro assump_31
    cases assump_31
    case inl assump_32 =>
      cases assump_32
      case inl assump_34 =>
        apply Or.inr
        apply Or.inl
        exact assump_34
      case inr assump_35 =>
        apply Or.inr
        apply Or.inr
        apply True.intro
    case inr assump_33 =>
      cases assump_33
      case inl assump_40 =>
        apply Or.inr
        apply Or.inr
        apply True.intro
      case inr assump_41 =>
        apply Or.inr
        apply Or.inr
        apply True.intro
  case inr assump_28 =>
    cases assump_28
    case inl assump_46 =>
      cases assump_46
      case intro assump_48 assump_49 =>
        cases assump_48
        case inl assump_50 =>
          cases assump_49
          case inl assump_54 =>
            apply Or.inl
            intro assump_58
            cases assump_58
            case inl assump_59 =>
              cases assump_59
              case inl assump_61 =>
                apply Or.inl
                apply And.intro
                apply True.intro
                exact assump_50
              case inr assump_62 =>
                apply Or.inl
                apply And.intro
                apply True.intro
                exact assump_50
            case inr assump_60 =>
              cases assump_60
              case inl assump_67 =>
                apply Or.inl
                apply And.intro
                apply True.intro
                exact assump_50
              case inr assump_68 =>
                apply Or.inl
                apply And.intro
                apply True.intro
                exact assump_50
          case inr assump_55 =>
            apply Or.inl
            intro assump_75
            cases assump_75
            case inl assump_76 =>
              cases assump_76
              case inl assump_78 =>
                apply Or.inl
                apply And.intro
                apply True.intro
                exact assump_50
              case inr assump_79 =>
                apply Or.inl
                apply And.intro
                apply True.intro
                exact assump_50
            case inr assump_77 =>
              cases assump_77
              case inl assump_84 =>
                apply Or.inl
                apply And.intro
                apply True.intro
                exact assump_50
              case inr assump_85 =>
                apply Or.inl
                apply And.intro
                apply True.intro
                exact assump_50
        case inr assump_51 =>
          apply False.elim assump_51
    case inr assump_47 =>
      cases assump_47
      case intro assump_92 assump_93 =>
        cases assump_92
        case inl assump_94 =>
          cases assump_93
          case inl assump_98 =>
            apply False.elim assump_98
          case inr assump_99 =>
            apply False.elim assump_99
        case inr assump_95 =>
          cases assump_93
          case inl assump_106 =>
            apply False.elim assump_106
          case inr assump_107 =>
            apply False.elim assump_107


variable (p5 p1 p0 p3 : Prop)
theorem file62_23722 : (((((True ∨ p1) → False) → False) → False) → ((((p1 → p3) → (True ∨ p3)) ∧ ((True → False) ∧ (p5 → p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      have assump_26 : (((True ∨ p1) → False) → False) := by
        intro assump_16
        have assump_27 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_19 := assump_16 assump_27
        apply False.elim assump_19
      let assump_15 := assump_1 assump_26
      apply False.elim assump_15


variable (p4 p3 p1 p7 p6 : Prop)
theorem file62_24373 : ((((((p7 → True) → False) → ((p3 ∨ p6) → False)) ∨ (((p4 ∧ True) ∧ (p1 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p7 → True) → False) → ((p3 ∨ p6) → False)) ∨ (((p4 ∧ True) ∧ (p1 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_31 : (p7 → True) := by
        intro assump_14
        apply True.intro
      let assump_13 := assump_5 assump_31
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_32 : (p7 → True) := by
        intro assump_23
        apply True.intro
      let assump_22 := assump_5 assump_32
      apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p0 p6 p5 p3 p4 p1 p7 : Prop)
theorem file62_25201 : (((((p5 ∧ p4) ∧ (p3 ∧ p6)) → ((False ∨ p3) ∨ (True ∨ p4))) ∧ (((p1 ∧ False) → False) ∨ ((p6 → False) ∧ (False ∧ p4)))) ∨ ((((False ∨ p5) ∨ (p6 → False)) ∨ ((p7 ∨ False) ∧ (p0 → p5))) → (((p3 → False) ∧ (p7 → False)) ∨ ((p4 → False) ∧ (p1 → p7))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inr
        exact assump_10
  apply Or.inl
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    apply False.elim assump_18


variable (p4 p5 p3 p7 p2 p0 p1 p6 : Prop)
theorem file62_25922 : ((((((p1 → False) ∧ (p4 ∨ p2)) → False) ∧ (((p6 → False) ∧ (p7 → False)) → ((p0 ∨ p6) → (p5 ∧ p4)))) ∧ ((((p1 ∧ p6) → (p5 → p1)) → False) ∧ (((p4 ∨ p6) ∧ (False → p6)) ∧ ((p3 ∨ p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              have assump_66 : ((p1 ∧ p6) → (p5 → p1)) := by
                intro assump_30
                intro assump_31
                cases assump_30
                case intro assump_34 assump_35 =>
                  exact assump_34
              let assump_29 := assump_10 assump_66
              apply False.elim assump_29
            case inr assump_19 =>
              have assump_67 : ((p1 ∧ p6) → (p5 → p1)) := by
                intro assump_53
                intro assump_54
                cases assump_53
                case intro assump_57 assump_58 =>
                  exact assump_57
              let assump_52 := assump_10 assump_67
              apply False.elim assump_52


variable (p0 p3 p7 p6 p5 p2 : Prop)
theorem file62_27272 : (((((p0 ∨ p7) → False) ∧ ((True → False) ∧ (p2 → False))) → (((p0 ∨ False) → (p6 → p5)) ∨ ((False → p6) → False))) ∨ ((((False → p5) ∨ (False ∧ p3)) → ((False → False) → False)) → False)) := by
  apply Or.inl
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_24
    case intro assump_27 assump_28 =>
      apply Or.inl
      intro assump_33
      intro assump_34
      cases assump_33
      case inl assump_37 =>
        have assump_50 : True := by
          apply True.intro
        let assump_44 := assump_27 assump_50
        apply False.elim assump_44
      case inr assump_38 =>
        apply False.elim assump_38


variable (p5 p0 p2 p6 p4 p7 p3 : Prop)
theorem file62_27993 : ((((((p3 → False) ∧ (p0 ∨ p0)) ∧ ((p3 → False) → (p2 → False))) → False) ∧ ((((p7 → True) → (p3 ∧ p5)) → ((p6 → False) → (p4 → p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_26 : (((p7 → True) → (p3 ∧ p5)) → ((p6 → False) → (p4 → p5))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      have assump_27 : (p7 → True) := by
        intro assump_19
        apply True.intro
      let assump_18 := assump_9 assump_27
      let assump_20 := And.right assump_18
      exact assump_20
    let assump_8 := assump_3 assump_26
    apply False.elim assump_8


variable (p1 p2 p4 p7 p3 p5 p6 p0 : Prop)
theorem file62_28700 : (((((p4 ∧ p0) → (p4 ∨ p0)) → False) ∧ (((p5 → False) ∧ (p2 ∧ p0)) ∧ ((p2 ∨ p4) → (p6 ∧ p3)))) → ((((p1 → p3) ∧ (p7 → False)) ∨ ((True → False) ∨ (p2 → False))) → (((False ∨ p5) → (p4 ∨ p3)) → False))) := by
  intro assump_41
  intro assump_42
  intro assump_43
  cases assump_42
  case inl assump_46 =>
    cases assump_46
    case intro assump_48 assump_49 =>
      cases assump_41
      case intro assump_54 assump_55 =>
        cases assump_55
        case intro assump_58 assump_59 =>
          cases assump_58
          case intro assump_60 assump_61 =>
            cases assump_61
            case intro assump_64 assump_65 =>
              have assump_168 : ((p4 ∧ p0) → (p4 ∨ p0)) := by
                intro assump_80
                cases assump_80
                case intro assump_81 assump_82 =>
                  apply Or.inl
                  exact assump_81
              let assump_79 := assump_54 assump_168
              apply False.elim assump_79
  case inr assump_47 =>
    cases assump_47
    case inl assump_90 =>
      cases assump_41
      case intro assump_94 assump_95 =>
        cases assump_95
        case intro assump_98 assump_99 =>
          cases assump_98
          case intro assump_100 assump_101 =>
            cases assump_101
            case intro assump_104 assump_105 =>
              have assump_169 : ((p4 ∧ p0) → (p4 ∨ p0)) := by
                intro assump_120
                cases assump_120
                case intro assump_121 assump_122 =>
                  apply Or.inl
                  exact assump_121
              let assump_119 := assump_94 assump_169
              apply False.elim assump_119
    case inr assump_91 =>
      cases assump_41
      case intro assump_132 assump_133 =>
        cases assump_133
        case intro assump_136 assump_137 =>
          cases assump_136
          case intro assump_138 assump_139 =>
            cases assump_139
            case intro assump_142 assump_143 =>
              have assump_170 : ((p4 ∧ p0) → (p4 ∨ p0)) := by
                intro assump_158
                cases assump_158
                case intro assump_159 assump_160 =>
                  apply Or.inl
                  exact assump_159
              let assump_157 := assump_132 assump_170
              apply False.elim assump_157


variable (p2 p4 p0 p3 p6 p7 p1 p5 : Prop)
theorem file62_31072 : (((((p0 → p2) → (p4 ∧ p3)) → False) → (((p5 ∨ p1) ∨ (p6 → True)) ∨ ((p0 → p6) → False))) ∨ ((((True ∨ p3) ∧ (p2 ∧ p6)) → ((False ∧ p7) ∧ (p1 ∧ p7))) → (((p2 ∨ p3) → (p3 ∨ False)) ∧ ((False → p7) ∨ (p2 → p5))))) := by
  apply Or.inl
  intro assump_37
  apply Or.inl
  apply Or.inr
  intro assump_40
  apply True.intro


variable (p3 p6 p4 p0 p1 p7 p5 : Prop)
theorem file62_31452 : (((((p4 → p3) → (p1 → False)) → False) → (((p4 ∨ p6) → (False → p7)) → False)) → ((((p5 → p7) ∧ (p4 ∧ False)) → ((p0 → False) ∧ (p1 ∨ True))) ∨ (((p4 → False) → False) ∧ ((p0 ∨ p5) → (p3 ∧ p5))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
  cases assump_4
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      apply False.elim assump_23


variable (p4 p7 p5 p3 p1 p6 p0 : Prop)
theorem file62_32087 : ((((((p4 → p7) → False) → ((True ∧ p0) → False)) ∧ (((True ∧ p4) ∧ (p6 → False)) ∨ ((p3 ∧ p4) → (p5 → True)))) ∧ ((((False → False) ∧ (False ∧ p1)) → ((p3 → False) → False)) → False)) → False) := by
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
          case intro assump_12 assump_13 =>
            have assump_58 : (((False → False) ∧ (False ∧ p1)) → ((p3 → False) → False)) := by
              intro assump_23
              intro assump_24
              cases assump_23
              case intro assump_27 assump_28 =>
                cases assump_28
                case intro assump_31 assump_32 =>
                  apply False.elim assump_31
            let assump_22 := assump_3 assump_58
            apply False.elim assump_22
      case inr assump_9 =>
        have assump_59 : (((False → False) ∧ (False ∧ p1)) → ((p3 → False) → False)) := by
          intro assump_43
          intro assump_44
          cases assump_43
          case intro assump_47 assump_48 =>
            cases assump_48
            case intro assump_51 assump_52 =>
              apply False.elim assump_51
        let assump_42 := assump_3 assump_59
        apply False.elim assump_42


variable (p6 p0 p1 p2 p7 p5 : Prop)
theorem file62_33533 : (((((p0 ∨ p1) ∨ (p7 → p5)) → ((p2 ∨ p7) → (p2 → p2))) ∨ (((True ∨ p7) ∧ (p6 ∧ False)) ∧ ((True → False) ∨ (False → False)))) → ((((True ∧ p5) ∧ (False ∧ p6)) ∧ ((p7 ∨ p6) ∧ (p5 ∨ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case intro assump_13 assump_14 =>
          apply False.elim assump_13


variable (p2 p0 p6 p5 p7 p3 p1 : Prop)
theorem file62_34098 : ((((((True → p0) ∧ (p6 ∧ p2)) ∧ ((p7 ∧ p2) ∧ (p1 → False))) → (((p7 ∧ p6) ∨ (p2 → False)) ∨ ((p5 ∨ p3) ∧ (False ∨ True)))) → False) → False) := by
  intro assump_16
  have assump_46 : ((((True → p0) ∧ (p6 ∧ p2)) ∧ ((p7 ∧ p2) ∧ (p1 → False))) → (((p7 ∧ p6) ∨ (p2 → False)) ∨ ((p5 ∨ p3) ∧ (False ∨ True)))) := by
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_24
        case intro assump_27 assump_28 =>
          cases assump_22
          case intro assump_33 assump_34 =>
            cases assump_33
            case intro assump_35 assump_36 =>
              apply Or.inl
              apply Or.inl
              apply And.intro
              exact assump_35
              exact assump_27
  let assump_19 := assump_16 assump_46
  apply False.elim assump_19


variable (p4 p5 p3 p6 : Prop)
theorem file62_35025 : (((((p3 → True) ∨ (p6 ∧ p4)) ∨ ((True → p4) ∧ (p5 ∧ True))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p3 → True) ∨ (p6 ∧ p4)) ∨ ((True → p4) ∧ (p5 ∧ True))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p0 p6 p7 p1 p2 p5 p3 : Prop)
theorem file62_35409 : (((((True ∨ p6) → False) → False) → False) → ((((False → False) ∧ (False ∧ p1)) → ((True → False) ∧ (p2 ∨ p0))) ∨ (((p3 → p3) → (p6 → False)) → ((p3 → p5) → (p6 → p7))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  cases assump_4
  case intro assump_16 assump_17 =>
    cases assump_17
    case intro assump_20 assump_21 =>
      apply False.elim assump_20


variable (p7 p4 p5 p6 p3 : Prop)
theorem file62_36012 : (((((p5 → False) ∧ (p5 ∧ p4)) → ((p3 ∧ p6) → False)) → (((p3 ∧ p3) → False) ∧ ((p7 → False) ∧ (p7 ∨ p3)))) → False) := by
  intro assump_1
  have assump_104 : (((p5 → False) ∧ (p5 ∧ p4)) → ((p3 ∧ p6) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          have assump_105 : p5 := by
            exact assump_17
          let assump_25 := assump_13 assump_105
          apply False.elim assump_25
  let assump_4 := assump_1 assump_104
  let assump_29 := And.right assump_4
  let assump_31 := And.right assump_29
  cases assump_31
  case inl assump_34 =>
    have assump_106 : (((p5 → False) ∧ (p5 ∧ p4)) → ((p3 ∧ p6) → False)) := by
      intro assump_40
      intro assump_41
      cases assump_41
      case intro assump_42 assump_43 =>
        cases assump_40
        case intro assump_48 assump_49 =>
          cases assump_49
          case intro assump_52 assump_53 =>
            have assump_107 : p5 := by
              exact assump_52
            let assump_60 := assump_48 assump_107
            apply False.elim assump_60
    let assump_39 := assump_1 assump_106
    let assump_64 := And.right assump_39
    let assump_66 := And.left assump_64
    have assump_108 : p7 := by
      exact assump_34
    let assump_67 := assump_66 assump_108
    apply False.elim assump_67
  case inr assump_35 =>
    have assump_109 : (((p5 → False) ∧ (p5 ∧ p4)) → ((p3 ∧ p6) → False)) := by
      intro assump_75
      intro assump_76
      cases assump_76
      case intro assump_77 assump_78 =>
        cases assump_75
        case intro assump_83 assump_84 =>
          cases assump_84
          case intro assump_87 assump_88 =>
            have assump_110 : p5 := by
              exact assump_87
            let assump_95 := assump_83 assump_110
            apply False.elim assump_95
    let assump_74 := assump_1 assump_109
    let assump_99 := And.left assump_74
    have assump_111 : (p3 ∧ p3) := by
      apply And.intro
      exact assump_35
      exact assump_35
    let assump_100 := assump_99 assump_111
    apply False.elim assump_100


variable (p6 p2 p5 p0 p4 p1 : Prop)
theorem file62_38305 : ((((((True → False) → (p6 → False)) ∨ ((p2 → False) ∨ (p2 → p5))) ∨ (((p0 → p2) ∧ (p1 ∧ p4)) ∨ ((False → False) ∧ (p5 → False)))) → ((((p5 → False) ∧ (True ∧ p5)) → False) → False)) → False) := by
  intro assump_4
  have assump_38 : ((((True → False) → (p6 → False)) ∨ ((p2 → False) ∨ (p2 → p5))) ∨ (((p0 → p2) ∧ (p1 ∧ p4)) ∨ ((False → False) ∧ (p5 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_39 : True := by
      apply True.intro
    let assump_14 := assump_8 assump_39
    apply False.elim assump_14
  let assump_7 := assump_4 assump_38
  have assump_40 : (((p5 → False) ∧ (True ∧ p5)) → False) := by
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      cases assump_21
      case intro assump_24 assump_25 =>
        have assump_41 : p5 := by
          exact assump_25
        let assump_31 := assump_20 assump_41
        apply False.elim assump_31
  let assump_18 := assump_7 assump_40
  apply False.elim assump_18


variable (p6 p0 p7 : Prop)
theorem file62_39369 : (((((p0 → p6) ∧ (False ∧ p6)) → ((True ∨ True) ∧ (p7 ∧ False))) → False) → False) := by
  intro assump_1
  have assump_33 : (((p0 → p6) ∧ (False ∧ p6)) → ((True ∨ True) ∧ (p7 ∧ False))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    apply And.intro
    cases assump_5
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
    cases assump_5
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p2 p3 p4 p5 p1 p7 p0 : Prop)
theorem file62_40207 : (((((p5 ∨ p0) ∧ (False ∧ True)) → False) ∨ (((p3 → p3) → False) ∨ ((p0 ∧ p3) → (p5 ∧ p2)))) ∨ ((((False ∧ p5) ∨ (p1 ∨ True)) ∧ ((p4 → True) → False)) ∨ (((p5 ∨ p7) → False) ∧ ((p1 → False) → (p2 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    case inr assump_5 =>
      cases assump_3
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p3 p6 p7 p2 p0 p1 p5 p4 : Prop)
theorem file62_40840 : (((((p1 ∨ p5) → (True → False)) ∨ ((p1 ∧ True) ∨ (True ∧ True))) ∧ (((p1 ∨ p5) → (p4 → False)) ∧ ((False → p7) → False))) → ((((p3 ∧ p3) → (p6 ∨ p5)) → False) ∨ (((p7 ∧ p4) → (p2 → p0)) → False))) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case inl assump_12 =>
      cases assump_11
      case intro assump_16 assump_17 =>
        apply Or.inl
        intro assump_22
        have assump_81 : (False → p7) := by
          intro assump_27
          apply False.elim assump_27
        let assump_26 := assump_17 assump_81
        apply False.elim assump_26
    case inr assump_13 =>
      cases assump_13
      case inl assump_33 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          cases assump_11
          case intro assump_41 assump_42 =>
            apply Or.inl
            intro assump_47
            have assump_82 : (False → p7) := by
              intro assump_52
              apply False.elim assump_52
            let assump_51 := assump_42 assump_82
            apply False.elim assump_51
      case inr assump_34 =>
        cases assump_34
        case intro assump_58 assump_59 =>
          cases assump_11
          case intro assump_64 assump_65 =>
            apply Or.inl
            intro assump_70
            have assump_83 : (False → p7) := by
              intro assump_75
              apply False.elim assump_75
            let assump_74 := assump_65 assump_83
            apply False.elim assump_74


variable (p0 p5 p6 p2 p3 : Prop)
theorem file62_42406 : ((((((p5 → False) → (p6 ∨ p0)) → False) → (((p2 ∧ False) → False) ∨ ((p6 ∨ True) ∧ (p0 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 → False) → (p6 ∨ p0)) → False) → (((p2 ∧ False) → False) ∨ ((p6 ∨ True) ∧ (p0 ∨ p3)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p4 p2 p7 p5 p0 p3 : Prop)
theorem file62_42934 : (((((p0 ∧ p0) ∧ (p3 ∧ False)) → ((p5 ∧ p3) ∧ (True ∨ True))) → (((False ∨ p5) → False) → ((True ∨ p4) ∨ (True → p3)))) ∨ ((((p6 → False) → (p7 ∨ p2)) ∧ ((p2 ∧ p4) → False)) ∧ (((True → False) → False) ∧ ((p3 ∧ p6) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p7 p3 p1 p5 : Prop)
theorem file62_43318 : ((((((p3 → p7) ∧ (p1 → p7)) → False) → (((p7 → False) ∨ (p5 → False)) → ((True ∨ p3) ∧ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p3 → p7) ∧ (p1 → p7)) → False) → (((p7 → False) ∨ (p5 → False)) → ((True ∨ p3) ∧ (False → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply True.intro
    intro assump_17
    apply False.elim assump_17
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p4 p5 p6 p1 : Prop)
theorem file62_43978 : ((((((p2 ∧ p1) → False) ∧ ((p5 → p2) → (p5 ∨ p4))) → False) ∧ ((((p6 ∨ p6) → False) → ((p5 ∨ p2) ∨ (p5 → p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_27 : (((p6 ∨ p6) → False) → ((p5 ∨ p2) ∨ (p5 → p6))) := by
      intro assump_9
      apply Or.inr
      intro assump_12
      have assump_28 : (((p6 ∨ p6) → False) → ((p5 ∨ p2) ∨ (p5 → p6))) := by
        intro assump_18
        apply Or.inl
        apply Or.inl
        exact assump_12
      let assump_17 := assump_3 assump_28
      apply False.elim assump_17
    let assump_8 := assump_3 assump_27
    apply False.elim assump_8


variable (p6 p4 p0 p3 p1 : Prop)
theorem file62_44687 : (((((p0 ∨ p3) ∨ (p1 → True)) → False) → False) ∨ ((((False → p1) ∨ (p4 ∨ p3)) ∨ ((True → p3) ∨ (p6 ∨ p1))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p0 ∨ p3) ∨ (p1 → True)) := by
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p1 p4 p2 p3 p5 p6 : Prop)
theorem file62_45073 : (((((p6 → p5) → False) → ((p4 ∨ p5) ∨ (p4 ∧ p4))) ∨ (((p4 → False) → False) → False)) → ((((p4 → True) ∨ (p1 → False)) ∧ ((p4 → False) ∧ (False ∧ p3))) → (((p2 → p5) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
    case inr assump_9 =>
      cases assump_7
      case intro assump_22 assump_23 =>
        cases assump_23
        case intro assump_26 assump_27 =>
          apply False.elim assump_26


variable (p2 p3 p4 p0 p7 p5 p1 : Prop)
theorem file62_45827 : (((((True ∨ p1) ∧ (p5 ∧ False)) → ((p4 ∧ p7) ∧ (p1 ∧ p2))) ∨ (((False ∨ p3) → (p7 ∨ p3)) ∧ ((p0 → p7) → (p2 → True)))) → ((((p5 → p2) → (False → p3)) → False) → (((True → False) → False) → ((False → False) ∨ (p7 ∧ False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  case inr assump_9 =>
    cases assump_9
    case intro assump_15 assump_16 =>
      apply Or.inl
      intro assump_21
      apply False.elim assump_21


variable (p0 p2 p3 p1 : Prop)
theorem file62_46425 : (((((p3 ∨ False) → (p1 ∧ p1)) → False) → False) → ((((True → False) → False) → False) → (((p2 → True) → (p0 → p0)) ∨ ((p3 → False) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  exact assump_8


variable (p2 p3 p4 p5 p0 : Prop)
theorem file62_46731 : (((((p5 → True) ∨ (p2 → p3)) → False) ∨ (((True ∨ p0) ∨ (p4 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_17 : ((p5 → True) ∨ (p2 → p3)) := by
      apply Or.inl
      intro assump_7
      apply True.intro
    let assump_6 := assump_2 assump_17
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_18 : ((True ∨ p0) ∨ (p4 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_13 := assump_3 assump_18
    apply False.elim assump_13


variable (p7 p2 p1 p3 p4 p0 p5 p6 : Prop)
theorem file62_47345 : ((((((p6 → p7) ∧ (p3 ∧ True)) ∧ ((False ∧ False) ∨ (p1 ∨ p3))) ∧ (((False → p1) ∧ (p2 ∨ False)) ∧ ((p6 → False) ∧ (p2 → p6)))) ∧ ((((p7 ∧ p5) ∧ (True ∧ p5)) → ((p4 → False) ∧ (p7 ∨ p0))) ∧ (((p6 → p1) ∨ (True ∧ True)) ∧ ((False → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_7
            case inl assump_18 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
            case inr assump_19 =>
              cases assump_19
              case inl assump_24 =>
                cases assump_5
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_31
                    case inl assump_34 =>
                      cases assump_29
                      case intro assump_38 assump_39 =>
                        cases assump_3
                        case intro assump_44 assump_45 =>
                          cases assump_45
                          case intro assump_48 assump_49 =>
                            cases assump_48
                            case inl assump_50 =>
                              have assump_134 : (False → False) := by
                                intro assump_57
                                apply False.elim assump_57
                              let assump_56 := assump_49 assump_134
                              apply False.elim assump_56
                            case inr assump_51 =>
                              cases assump_51
                              case intro assump_63 assump_64 =>
                                have assump_135 : (False → False) := by
                                  intro assump_72
                                  apply False.elim assump_72
                                let assump_71 := assump_49 assump_135
                                apply False.elim assump_71
                    case inr assump_35 =>
                      apply False.elim assump_35
              case inr assump_25 =>
                cases assump_5
                case intro assump_82 assump_83 =>
                  cases assump_82
                  case intro assump_84 assump_85 =>
                    cases assump_85
                    case inl assump_88 =>
                      cases assump_83
                      case intro assump_92 assump_93 =>
                        cases assump_3
                        case intro assump_98 assump_99 =>
                          cases assump_99
                          case intro assump_102 assump_103 =>
                            cases assump_102
                            case inl assump_104 =>
                              have assump_136 : (False → False) := by
                                intro assump_111
                                apply False.elim assump_111
                              let assump_110 := assump_103 assump_136
                              apply False.elim assump_110
                            case inr assump_105 =>
                              cases assump_105
                              case intro assump_117 assump_118 =>
                                have assump_137 : (False → False) := by
                                  intro assump_126
                                  apply False.elim assump_126
                                let assump_125 := assump_103 assump_137
                                apply False.elim assump_125
                    case inr assump_89 =>
                      apply False.elim assump_89


variable (p6 p1 p7 p2 p3 p4 : Prop)
theorem file62_51313 : (((((p1 ∨ p6) ∨ (p1 → p4)) → ((True ∨ False) ∨ (p3 ∧ True))) → False) → ((((p1 → p7) ∧ (p7 → p4)) → False) → (((p2 ∧ False) ∧ (p3 → False)) ∨ ((p1 ∧ True) → (p2 → p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inr
  intro assump_7
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    have assump_34 : (((p1 ∨ p6) ∨ (p1 → p4)) → ((True ∨ False) ∨ (p3 ∧ True))) := by
      intro assump_20
      cases assump_20
      case inl assump_21 =>
        cases assump_21
        case inl assump_23 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_24 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_22 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    let assump_19 := assump_1 assump_34
    apply False.elim assump_19


variable (p3 p0 p1 : Prop)
theorem file62_52231 : ((((((p1 → p0) → False) ∧ ((False → p3) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p1 → p0) → False) ∧ ((False → p3) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_23 : (False → p3) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p1 p7 p3 p2 p4 p0 p5 : Prop)
theorem file62_52794 : (((((p1 → False) ∧ (p3 → p0)) ∧ ((p3 → p3) ∧ (p7 ∧ p6))) → (((False ∨ p2) ∨ (p3 → False)) → False)) → ((((p5 ∨ p7) ∨ (p6 ∨ p0)) ∧ ((False ∧ p3) ∧ (p4 → p3))) → (((False → True) → False) → ((p0 → False) ∧ (p5 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
      case inr assump_14 =>
        cases assump_10
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            apply False.elim assump_27
    case inr assump_12 =>
      cases assump_12
      case inl assump_31 =>
        cases assump_10
        case intro assump_35 assump_36 =>
          cases assump_35
          case intro assump_37 assump_38 =>
            apply False.elim assump_37
      case inr assump_32 =>
        cases assump_10
        case intro assump_43 assump_44 =>
          cases assump_43
          case intro assump_45 assump_46 =>
            apply False.elim assump_45
  apply And.intro
  cases assump_2
  case intro assump_51 assump_52 =>
    cases assump_51
    case inl assump_53 =>
      cases assump_53
      case inl assump_55 =>
        cases assump_52
        case intro assump_59 assump_60 =>
          cases assump_59
          case intro assump_61 assump_62 =>
            apply False.elim assump_61
      case inr assump_56 =>
        cases assump_52
        case intro assump_67 assump_68 =>
          cases assump_67
          case intro assump_69 assump_70 =>
            apply False.elim assump_69
    case inr assump_54 =>
      cases assump_54
      case inl assump_73 =>
        cases assump_52
        case intro assump_77 assump_78 =>
          cases assump_77
          case intro assump_79 assump_80 =>
            apply False.elim assump_79
      case inr assump_74 =>
        cases assump_52
        case intro assump_85 assump_86 =>
          cases assump_85
          case intro assump_87 assump_88 =>
            apply False.elim assump_87
  cases assump_2
  case intro assump_93 assump_94 =>
    cases assump_93
    case inl assump_95 =>
      cases assump_95
      case inl assump_97 =>
        cases assump_94
        case intro assump_101 assump_102 =>
          cases assump_101
          case intro assump_103 assump_104 =>
            apply False.elim assump_103
      case inr assump_98 =>
        cases assump_94
        case intro assump_109 assump_110 =>
          cases assump_109
          case intro assump_111 assump_112 =>
            apply False.elim assump_111
    case inr assump_96 =>
      cases assump_96
      case inl assump_115 =>
        cases assump_94
        case intro assump_119 assump_120 =>
          cases assump_119
          case intro assump_121 assump_122 =>
            apply False.elim assump_121
      case inr assump_116 =>
        cases assump_94
        case intro assump_127 assump_128 =>
          cases assump_127
          case intro assump_129 assump_130 =>
            apply False.elim assump_129


variable (p6 p1 p3 p2 p7 : Prop)
theorem file62_56146 : ((((((p3 ∧ False) ∧ (p6 → False)) → ((True → False) ∨ (p7 ∨ True))) → (((False → False) ∨ (p3 → False)) ∨ ((p2 ∧ True) ∨ (p1 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p3 ∧ False) ∧ (p6 → False)) → ((True → False) ∨ (p7 ∨ True))) → (((False → False) ∨ (p3 → False)) ∨ ((p2 ∧ True) ∨ (p1 ∧ True)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p0 p7 p4 p5 p6 p2 : Prop)
theorem file62_56712 : ((((((p5 → False) → (p1 → p0)) ∧ ((p2 ∨ p6) → False)) ∨ (((p7 ∨ p1) ∧ (p7 → False)) → False)) ∧ ((((p2 → False) → (p6 → False)) ∧ ((p5 ∧ False) ∧ (p4 → p7))) ∧ (((p7 ∨ p5) ∧ (p2 → p7)) → ((p7 ∨ True) → (p1 ∨ p1))))) → False) := by
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
                apply False.elim assump_21
    case inr assump_5 =>
      cases assump_3
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              apply False.elim assump_37


variable (p2 p7 p4 p5 : Prop)
theorem file62_57835 : (((((p5 → p2) ∧ (p5 → False)) ∨ ((p7 ∨ True) → False)) ∧ (((p4 → p4) → False) ∧ ((False ∧ False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          have assump_42 : (p4 → p4) := by
            intro assump_20
            exact assump_20
          let assump_19 := assump_12 assump_42
          apply False.elim assump_19
    case inr assump_5 =>
      cases assump_3
      case intro assump_28 assump_29 =>
        have assump_43 : (p4 → p4) := by
          intro assump_36
          exact assump_36
        let assump_35 := assump_28 assump_43
        apply False.elim assump_35


variable (p1 p0 p3 : Prop)
theorem file62_58687 : ((((((False → p0) → False) ∧ ((p0 → p3) ∨ (p3 ∧ p1))) → (((p0 ∧ p3) ∨ (p3 ∧ p0)) ∧ ((False → False) → (p3 → False)))) → False) → False) := by
  intro assump_15
  have assump_91 : ((((False → p0) → False) ∧ ((p0 → p3) ∨ (p3 ∧ p1))) → (((p0 ∧ p3) ∨ (p3 ∧ p0)) ∧ ((False → False) → (p3 → False)))) := by
    intro assump_19
    apply And.intro
    cases assump_19
    case intro assump_20 assump_21 =>
      cases assump_21
      case inl assump_24 =>
        have assump_92 : (False → p0) := by
          intro assump_30
          apply False.elim assump_30
        let assump_29 := assump_20 assump_92
        apply False.elim assump_29
      case inr assump_25 =>
        cases assump_25
        case intro assump_36 assump_37 =>
          have assump_93 : (False → p0) := by
            intro assump_45
            apply False.elim assump_45
          let assump_44 := assump_20 assump_93
          apply False.elim assump_44
    intro assump_51
    intro assump_52
    cases assump_19
    case intro assump_57 assump_58 =>
      cases assump_58
      case inl assump_61 =>
        have assump_94 : (False → p0) := by
          intro assump_67
          apply False.elim assump_67
        let assump_66 := assump_57 assump_94
        apply False.elim assump_66
      case inr assump_62 =>
        cases assump_62
        case intro assump_73 assump_74 =>
          have assump_95 : (False → p0) := by
            intro assump_82
            apply False.elim assump_82
          let assump_81 := assump_57 assump_95
          apply False.elim assump_81
  let assump_18 := assump_15 assump_91
  apply False.elim assump_18


variable (p0 p1 p4 p5 p2 p6 : Prop)
theorem file62_60368 : (((((p1 ∨ p1) ∧ (p1 → False)) ∧ ((p6 → p1) ∧ (p5 ∧ p4))) ∧ (((False ∨ p2) → (p6 → True)) ∧ ((False → p6) ∧ (p5 → False)))) → ((((p6 ∧ p0) → False) → False) → False)) := by
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
          cases assump_8
          case intro assump_17 assump_18 =>
            cases assump_18
            case intro assump_21 assump_22 =>
              cases assump_6
              case intro assump_27 assump_28 =>
                cases assump_28
                case intro assump_31 assump_32 =>
                  have assump_69 : p5 := by
                    exact assump_21
                  let assump_37 := assump_32 assump_69
                  apply False.elim assump_37
        case inr assump_12 =>
          cases assump_8
          case intro assump_45 assump_46 =>
            cases assump_46
            case intro assump_49 assump_50 =>
              cases assump_6
              case intro assump_55 assump_56 =>
                cases assump_56
                case intro assump_59 assump_60 =>
                  have assump_70 : p5 := by
                    exact assump_49
                  let assump_65 := assump_60 assump_70
                  apply False.elim assump_65


variable (p3 p7 p5 p0 : Prop)
theorem file62_61841 : ((((((False ∨ p7) ∧ (p0 → False)) ∧ ((False ∧ p7) → (p3 ∨ False))) → (((p7 → False) ∧ (False ∧ p5)) → False)) → False) → False) := by
  intro assump_10
  have assump_27 : ((((False ∨ p7) ∧ (p0 → False)) ∧ ((False ∧ p7) → (p3 ∨ False))) → (((p7 → False) ∧ (False ∧ p5)) → False)) := by
    intro assump_14
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        apply False.elim assump_20
  let assump_13 := assump_10 assump_27
  apply False.elim assump_13


variable (p0 p6 p4 p1 p2 p3 : Prop)
theorem file62_62449 : (((((True → False) ∧ (p3 → False)) ∨ ((p0 → p3) → False)) ∧ (((p0 → False) ∧ (p6 ∧ p1)) ∧ ((p2 ∧ p4) ∨ (p2 ∨ p4)))) → ((((p3 → False) → (True ∨ p1)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_6
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_18
            case intro assump_21 assump_22 =>
              cases assump_16
              case inl assump_27 =>
                cases assump_27
                case intro assump_29 assump_30 =>
                  have assump_156 : True := by
                    apply True.intro
                  let assump_41 := assump_9 assump_156
                  apply False.elim assump_41
              case inr assump_28 =>
                cases assump_28
                case inl assump_45 =>
                  have assump_157 : True := by
                    apply True.intro
                  let assump_54 := assump_9 assump_157
                  apply False.elim assump_54
                case inr assump_46 =>
                  have assump_158 : True := by
                    apply True.intro
                  let assump_65 := assump_9 assump_158
                  apply False.elim assump_65
    case inr assump_8 =>
      cases assump_6
      case intro assump_71 assump_72 =>
        cases assump_71
        case intro assump_73 assump_74 =>
          cases assump_74
          case intro assump_77 assump_78 =>
            cases assump_72
            case inl assump_83 =>
              cases assump_83
              case intro assump_85 assump_86 =>
                have assump_159 : (p0 → p3) := by
                  intro assump_97
                  have assump_160 : p0 := by
                    exact assump_97
                  let assump_105 := assump_73 assump_160
                  apply False.elim assump_105
                let assump_96 := assump_8 assump_159
                apply False.elim assump_96
            case inr assump_84 =>
              cases assump_84
              case inl assump_112 =>
                have assump_161 : (p0 → p3) := by
                  intro assump_121
                  have assump_162 : p0 := by
                    exact assump_121
                  let assump_128 := assump_73 assump_162
                  apply False.elim assump_128
                let assump_120 := assump_8 assump_161
                apply False.elim assump_120
              case inr assump_113 =>
                have assump_163 : (p0 → p3) := by
                  intro assump_142
                  have assump_164 : p0 := by
                    exact assump_142
                  let assump_149 := assump_73 assump_164
                  apply False.elim assump_149
                let assump_141 := assump_8 assump_163
                apply False.elim assump_141


variable (p6 p7 p1 p0 : Prop)
theorem file62_65519 : (((((p0 ∧ p6) ∧ (p1 → False)) ∨ ((p1 ∨ p7) → (False → False))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p0 ∧ p6) ∧ (p1 → False)) ∨ ((p1 ∨ p7) → (False → False))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p1 p5 p0 p2 p7 p3 : Prop)
theorem file62_65922 : (((((p1 ∨ p5) ∨ (p3 → p7)) ∨ ((p3 ∧ p5) ∨ (p1 → p7))) → False) → ((((p3 → False) → False) → ((p0 ∧ False) → False)) ∨ (((p2 → False) → False) → ((False ∨ p4) ∧ (p2 → p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p6 p2 p7 p5 : Prop)
theorem file62_66303 : ((((((False → False) → (False → True)) → False) → (((p5 ∨ p2) → (p7 → True)) ∨ ((False → False) → (p7 → p6)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False → False) → (False → True)) → False) → (((p5 ∨ p2) → (p7 → True)) ∨ ((False → False) → (p7 → p6)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply True.intro
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p1 p2 p4 p6 p3 p5 p7 : Prop)
theorem file62_66812 : (((((False → p5) → False) → ((p6 → False) → (p3 → p2))) ∨ (((False → False) ∧ (False ∧ p3)) ∨ ((p1 ∨ p1) ∧ (p7 ∧ p6)))) ∨ ((((False ∨ False) ∧ (p4 ∧ p7)) → ((p7 → False) → (True → p2))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_17 : (False → p5) := by
    intro assump_11
    apply False.elim assump_11
  let assump_10 := assump_1 assump_17
  apply False.elim assump_10


variable (p6 p2 p4 p1 p0 p5 : Prop)
theorem file62_67311 : (((((p4 ∧ False) → (True → False)) → False) → (((p1 → p4) → False) → False)) ∨ ((((False → False) ∧ (p2 ∧ p5)) ∨ ((p2 → False) ∨ (p0 ∧ p4))) ∨ (((p4 → p6) → (p0 → p0)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_21 : ((p4 ∧ False) → (True → False)) := by
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
  let assump_7 := assump_1 assump_21
  apply False.elim assump_7


variable (p7 p5 p6 p2 p1 p4 p3 p0 : Prop)
theorem file62_67861 : (((((p1 ∨ p4) → False) → ((False → p2) ∨ (p3 → False))) → (((False ∧ p6) ∨ (True → False)) ∧ ((True ∨ True) ∧ (p0 ∨ p3)))) → ((((p2 → False) ∧ (p0 ∨ p3)) ∧ ((p0 → p7) → (p6 → p0))) ∨ (((p5 ∧ False) ∧ (True ∧ p7)) → False))) := by
  intro assump_1
  apply Or.inr
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      apply False.elim assump_33


variable (p6 p0 p7 p3 p2 p5 : Prop)
theorem file62_68346 : ((((((p3 ∧ p0) ∨ (False ∧ False)) ∧ ((p7 → False) ∧ (p5 ∨ p6))) ∨ (((p7 → False) ∧ (p2 → p0)) → ((False → False) → (p6 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 ∧ p0) ∨ (False ∧ False)) ∧ ((p7 → False) ∧ (p5 ∨ p6))) ∨ (((p7 → False) ∧ (p2 → p0)) → ((False → False) → (p6 ∨ True)))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p1 p3 p2 p7 p0 p6 : Prop)
theorem file62_68951 : (((((False → False) → False) → ((False → p7) ∧ (p4 ∨ p4))) ∧ (((p7 → True) ∨ (True ∧ p4)) ∨ ((p3 → p1) → (p2 ∨ p2)))) ∨ ((((p0 → False) ∧ (True → p6)) ∧ ((p1 → p6) ∧ (p6 ∨ p0))) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  apply And.intro
  intro assump_2
  apply False.elim assump_2
  have assump_15 : (False → False) := by
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_15
  apply False.elim assump_7
  apply Or.inl
  apply Or.inl
  intro assump_14
  apply True.intro


variable (p0 p6 p4 p2 p7 p3 p1 : Prop)
theorem file62_69543 : (((((False → False) → False) → ((False → True) ∧ (p0 ∧ p4))) → False) → ((((p6 → p3) → False) ∧ ((p1 ∧ p3) ∧ (p6 ∧ p4))) ∧ (((p2 → True) ∧ (p6 ∨ p3)) ∨ ((p7 → p0) → False)))) := by
  intro assump_13
  apply And.intro
  apply And.intro
  intro assump_14
  have assump_178 : (((False → False) → False) → ((False → True) ∧ (p0 ∧ p4))) := by
    intro assump_20
    apply And.intro
    intro assump_21
    apply True.intro
    apply And.intro
    have assump_179 : (False → False) := by
      intro assump_25
      apply False.elim assump_25
    let assump_24 := assump_20 assump_179
    apply False.elim assump_24
    have assump_180 : (False → False) := by
      intro assump_34
      apply False.elim assump_34
    let assump_33 := assump_20 assump_180
    apply False.elim assump_33
  let assump_19 := assump_13 assump_178
  apply False.elim assump_19
  apply And.intro
  apply And.intro
  have assump_181 : (((False → False) → False) → ((False → True) ∧ (p0 ∧ p4))) := by
    intro assump_46
    apply And.intro
    intro assump_47
    apply True.intro
    apply And.intro
    have assump_182 : (False → False) := by
      intro assump_51
      apply False.elim assump_51
    let assump_50 := assump_46 assump_182
    apply False.elim assump_50
    have assump_183 : (False → False) := by
      intro assump_60
      apply False.elim assump_60
    let assump_59 := assump_46 assump_183
    apply False.elim assump_59
  let assump_45 := assump_13 assump_181
  apply False.elim assump_45
  have assump_184 : (((False → False) → False) → ((False → True) ∧ (p0 ∧ p4))) := by
    intro assump_72
    apply And.intro
    intro assump_73
    apply True.intro
    apply And.intro
    have assump_185 : (False → False) := by
      intro assump_77
      apply False.elim assump_77
    let assump_76 := assump_72 assump_185
    apply False.elim assump_76
    have assump_186 : (False → False) := by
      intro assump_86
      apply False.elim assump_86
    let assump_85 := assump_72 assump_186
    apply False.elim assump_85
  let assump_71 := assump_13 assump_184
  apply False.elim assump_71
  apply And.intro
  have assump_187 : (((False → False) → False) → ((False → True) ∧ (p0 ∧ p4))) := by
    intro assump_98
    apply And.intro
    intro assump_99
    apply True.intro
    apply And.intro
    have assump_188 : (False → False) := by
      intro assump_103
      apply False.elim assump_103
    let assump_102 := assump_98 assump_188
    apply False.elim assump_102
    have assump_189 : (False → False) := by
      intro assump_112
      apply False.elim assump_112
    let assump_111 := assump_98 assump_189
    apply False.elim assump_111
  let assump_97 := assump_13 assump_187
  apply False.elim assump_97
  have assump_190 : (((False → False) → False) → ((False → True) ∧ (p0 ∧ p4))) := by
    intro assump_124
    apply And.intro
    intro assump_125
    apply True.intro
    apply And.intro
    have assump_191 : (False → False) := by
      intro assump_129
      apply False.elim assump_129
    let assump_128 := assump_124 assump_191
    apply False.elim assump_128
    have assump_192 : (False → False) := by
      intro assump_138
      apply False.elim assump_138
    let assump_137 := assump_124 assump_192
    apply False.elim assump_137
  let assump_123 := assump_13 assump_190
  apply False.elim assump_123
  apply Or.inr
  intro assump_150
  have assump_193 : (((False → False) → False) → ((False → True) ∧ (p0 ∧ p4))) := by
    intro assump_155
    apply And.intro
    intro assump_156
    apply True.intro
    apply And.intro
    have assump_194 : (False → False) := by
      intro assump_160
      apply False.elim assump_160
    let assump_159 := assump_155 assump_194
    apply False.elim assump_159
    have assump_195 : (False → False) := by
      intro assump_169
      apply False.elim assump_169
    let assump_168 := assump_155 assump_195
    apply False.elim assump_168
  let assump_154 := assump_13 assump_193
  apply False.elim assump_154


variable (p4 p5 p3 p0 p7 p2 p6 : Prop)
theorem file62_73577 : ((((((p5 ∨ p5) ∨ (p4 ∨ p4)) → ((p3 ∨ False) → (p7 → p7))) → False) ∧ ((((True → p0) ∨ (p3 ∨ p0)) ∧ ((p5 → False) ∧ (p3 → p2))) ∨ (((p3 → False) → (p6 ∨ p5)) ∧ ((False → False) → False)))) → False) := by
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
          case intro assump_14 assump_15 =>
            have assump_149 : (((p5 ∨ p5) ∨ (p4 ∨ p4)) → ((p3 ∨ False) → (p7 → p7))) := by
              intro assump_25
              intro assump_26
              intro assump_27
              cases assump_26
              case inl assump_30 =>
                cases assump_25
                case inl assump_34 =>
                  cases assump_34
                  case inl assump_36 =>
                    exact assump_27
                  case inr assump_37 =>
                    exact assump_27
                case inr assump_35 =>
                  cases assump_35
                  case inl assump_42 =>
                    exact assump_27
                  case inr assump_43 =>
                    exact assump_27
              case inr assump_31 =>
                apply False.elim assump_31
            let assump_24 := assump_2 assump_149
            apply False.elim assump_24
        case inr assump_11 =>
          cases assump_11
          case inl assump_53 =>
            cases assump_9
            case intro assump_57 assump_58 =>
              have assump_150 : (((p5 ∨ p5) ∨ (p4 ∨ p4)) → ((p3 ∨ False) → (p7 → p7))) := by
                intro assump_68
                intro assump_69
                intro assump_70
                cases assump_69
                case inl assump_73 =>
                  cases assump_68
                  case inl assump_77 =>
                    cases assump_77
                    case inl assump_79 =>
                      exact assump_70
                    case inr assump_80 =>
                      exact assump_70
                  case inr assump_78 =>
                    cases assump_78
                    case inl assump_85 =>
                      exact assump_70
                    case inr assump_86 =>
                      exact assump_70
                case inr assump_74 =>
                  apply False.elim assump_74
              let assump_67 := assump_2 assump_150
              apply False.elim assump_67
          case inr assump_54 =>
            cases assump_9
            case intro assump_98 assump_99 =>
              have assump_151 : (((p5 ∨ p5) ∨ (p4 ∨ p4)) → ((p3 ∨ False) → (p7 → p7))) := by
                intro assump_108
                intro assump_109
                intro assump_110
                cases assump_109
                case inl assump_113 =>
                  cases assump_108
                  case inl assump_117 =>
                    cases assump_117
                    case inl assump_119 =>
                      exact assump_110
                    case inr assump_120 =>
                      exact assump_110
                  case inr assump_118 =>
                    cases assump_118
                    case inl assump_125 =>
                      exact assump_110
                    case inr assump_126 =>
                      exact assump_110
                case inr assump_114 =>
                  apply False.elim assump_114
              let assump_107 := assump_2 assump_151
              apply False.elim assump_107
    case inr assump_7 =>
      cases assump_7
      case intro assump_136 assump_137 =>
        have assump_152 : (False → False) := by
          intro assump_143
          apply False.elim assump_143
        let assump_142 := assump_137 assump_152
        apply False.elim assump_142


variable (p6 p3 p4 p0 p1 p2 p7 : Prop)
theorem file62_77483 : (((((False ∨ p7) ∧ (p3 → False)) → False) → (((p4 ∨ False) ∧ (p2 → p6)) → ((p1 ∧ p1) → (False → False)))) ∨ ((((False → False) ∨ (p7 → False)) ∧ ((False → p1) → False)) → (((p1 ∧ p2) → (p0 → p7)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p4 p2 p1 p5 p6 p3 : Prop)
theorem file62_77867 : ((((((True ∧ p1) → False) → ((p6 → False) → (p4 → p4))) ∨ (((p3 ∧ p2) → (p2 ∨ p1)) ∧ ((p2 ∧ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((True ∧ p1) → False) → ((p6 → False) → (p4 → p4))) ∨ (((p3 ∧ p2) → (p2 ∨ p1)) ∧ ((p2 ∧ p5) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    exact assump_7
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p3 p7 p2 : Prop)
theorem file62_78354 : (((((False → False) → (p2 ∨ True)) → False) ∧ (((True ∨ False) ∨ (p7 → False)) → ((True ∨ p3) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((True ∨ False) ∨ (p7 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_13
    have assump_14 : (True ∨ p3) := by
      apply Or.inl
      apply True.intro
    let assump_9 := assump_8 assump_14
    apply False.elim assump_9


variable (p2 p7 p3 p6 p1 p4 : Prop)
theorem file62_78911 : (((((p3 ∧ p4) → False) ∧ ((False ∨ p2) → False)) → False) → ((((p2 → False) ∧ (p1 → False)) ∨ ((p2 → False) ∨ (p6 ∨ p6))) → (((p7 ∨ p6) → (p1 → False)) → ((True ∨ p4) ∨ (p2 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  case inr assump_7 =>
    cases assump_7
    case inl assump_16 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_17 =>
      cases assump_17
      case inl assump_22 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_23 =>
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p5 p1 p7 p3 p0 p4 : Prop)
theorem file62_79737 : ((((((p5 → False) ∨ (p3 ∧ p4)) → ((p3 ∨ p0) → False)) → False) ∧ ((((p1 ∨ p7) ∧ (p0 ∧ p5)) ∨ ((p0 ∧ p7) ∨ (True ∧ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (((p1 ∨ p7) ∧ (p0 ∧ p5)) ∨ ((p0 ∧ p7) ∨ (True ∧ True))) := by
      apply Or.inr
      apply Or.inr
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p2 p7 p1 p6 p0 p5 p3 p4 : Prop)
theorem file62_80276 : ((((((p7 → p7) ∧ (True ∨ p0)) ∧ ((p3 ∧ True) ∨ (False → p6))) ∨ (((p7 → False) ∨ (p2 → p2)) ∨ ((p7 → False) → (p4 → False)))) → ((((p0 → True) → (True ∧ True)) ∨ ((p5 ∧ p4) ∧ (p1 ∨ False))) → False)) → False) := by
  intro assump_5
  have assump_20 : ((((p7 → p7) ∧ (True ∨ p0)) ∧ ((p3 ∧ True) ∨ (False → p6))) ∨ (((p7 → False) ∨ (p2 → p2)) ∨ ((p7 → False) → (p4 → False)))) := by
    apply Or.inl
    apply And.intro
    apply And.intro
    intro assump_9
    exact assump_9
    apply Or.inl
    apply True.intro
    apply Or.inr
    intro assump_12
    apply False.elim assump_12
  let assump_8 := assump_5 assump_20
  have assump_21 : (((p0 → True) → (True ∧ True)) ∨ ((p5 ∧ p4) ∧ (p1 ∨ False))) := by
    apply Or.inl
    intro assump_16
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_15 := assump_8 assump_21
  apply False.elim assump_15


variable (p6 p0 p3 p2 p1 : Prop)
theorem file62_81204 : (((((p0 → False) → False) → ((p0 ∨ p3) → (p3 → False))) → (((p1 → p0) ∨ (False → p3)) → False)) → ((((p1 → False) → (p6 → False)) ∧ ((p2 ∨ p3) ∧ (p0 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
      case inr assump_10 =>
        cases assump_8
        case intro assump_21 assump_22 =>
          apply False.elim assump_22


variable (p0 p5 p2 p7 p1 p4 p3 p6 : Prop)
theorem file62_81866 : (((((p6 → p1) ∧ (p7 → p2)) ∧ ((p4 → p5) ∨ (p2 → False))) → (((False → p7) → False) → False)) ∨ ((((p1 ∧ p7) ∨ (p3 ∨ p2)) → ((p1 ∨ True) ∨ (p0 → False))) → (((False ∧ p0) ∧ (p1 → p7)) ∧ ((p5 ∨ p6) ∧ (p5 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case inl assump_13 =>
        have assump_39 : (False → p7) := by
          intro assump_21
          apply False.elim assump_21
        let assump_20 := assump_2 assump_39
        apply False.elim assump_20
      case inr assump_14 =>
        have assump_40 : (False → p7) := by
          intro assump_33
          apply False.elim assump_33
        let assump_32 := assump_2 assump_40
        apply False.elim assump_32


variable (p4 p6 p1 p5 p3 p0 p2 p7 : Prop)
theorem file62_82754 : (((((p3 ∨ False) ∨ (p7 → False)) → False) → (((p3 ∧ p5) ∧ (p5 ∨ p6)) → ((p1 → p6) ∧ (p2 → p6)))) ∨ ((((False → False) → (p4 → False)) → ((p3 ∨ p7) → (p4 → False))) ∨ (((p5 ∧ p3) ∨ (p0 → False)) ∨ ((p6 → p4) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case inl assump_14 =>
        have assump_53 : ((p3 ∨ False) ∨ (p7 → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_8
        let assump_20 := assump_1 assump_53
        apply False.elim assump_20
      case inr assump_15 =>
        exact assump_15
  intro assump_28
  cases assump_2
  case intro assump_31 assump_32 =>
    cases assump_31
    case intro assump_33 assump_34 =>
      cases assump_32
      case inl assump_39 =>
        have assump_54 : ((p3 ∨ False) ∨ (p7 → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_33
        let assump_45 := assump_1 assump_54
        apply False.elim assump_45
      case inr assump_40 =>
        exact assump_40


variable (p5 p1 p3 p0 : Prop)
theorem file62_83978 : ((((((p0 ∨ False) ∨ (p5 → True)) ∨ ((p1 ∧ p3) → (False → False))) ∨ (((True → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p0 ∨ False) ∨ (p5 → True)) ∨ ((p1 ∧ p3) → (False → False))) ∨ (((True → False) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p6 p5 p3 p7 p1 p0 p2 p4 : Prop)
theorem file62_84470 : (((((p3 ∧ p7) ∧ (p1 ∧ p3)) ∨ ((p3 → p1) → False)) ∨ (((True → p3) ∨ (True ∨ p3)) ∨ ((True ∧ p3) → (False ∧ p5)))) → ((((p2 ∧ False) ∨ (False ∧ p4)) → ((p6 → p0) → (p0 → False))) ∧ (((p1 → False) ∨ (p2 ∨ p7)) → ((p2 → p6) → (p1 ∨ True))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
  case inr assump_10 =>
    cases assump_10
    case intro assump_17 assump_18 =>
      apply False.elim assump_17
  intro assump_21
  intro assump_22
  cases assump_21
  case inl assump_25 =>
    cases assump_1
    case inl assump_29 =>
      cases assump_29
      case inl assump_31 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            cases assump_34
            case intro assump_41 assump_42 =>
              apply Or.inl
              exact assump_41
      case inr assump_32 =>
        apply Or.inr
        apply True.intro
    case inr assump_30 =>
      cases assump_30
      case inl assump_49 =>
        cases assump_49
        case inl assump_51 =>
          apply Or.inr
          apply True.intro
        case inr assump_52 =>
          cases assump_52
          case inl assump_55 =>
            apply Or.inr
            apply True.intro
          case inr assump_56 =>
            apply Or.inr
            apply True.intro
      case inr assump_50 =>
        apply Or.inr
        apply True.intro
  case inr assump_26 =>
    cases assump_26
    case inl assump_63 =>
      cases assump_1
      case inl assump_67 =>
        cases assump_67
        case inl assump_69 =>
          cases assump_69
          case intro assump_71 assump_72 =>
            cases assump_71
            case intro assump_73 assump_74 =>
              cases assump_72
              case intro assump_79 assump_80 =>
                apply Or.inl
                exact assump_79
        case inr assump_70 =>
          apply Or.inr
          apply True.intro
      case inr assump_68 =>
        cases assump_68
        case inl assump_87 =>
          cases assump_87
          case inl assump_89 =>
            apply Or.inr
            apply True.intro
          case inr assump_90 =>
            cases assump_90
            case inl assump_93 =>
              apply Or.inr
              apply True.intro
            case inr assump_94 =>
              apply Or.inr
              apply True.intro
        case inr assump_88 =>
          apply Or.inr
          apply True.intro
    case inr assump_64 =>
      cases assump_1
      case inl assump_103 =>
        cases assump_103
        case inl assump_105 =>
          cases assump_105
          case intro assump_107 assump_108 =>
            cases assump_107
            case intro assump_109 assump_110 =>
              cases assump_108
              case intro assump_115 assump_116 =>
                apply Or.inl
                exact assump_115
        case inr assump_106 =>
          apply Or.inr
          apply True.intro
      case inr assump_104 =>
        cases assump_104
        case inl assump_123 =>
          cases assump_123
          case inl assump_125 =>
            apply Or.inr
            apply True.intro
          case inr assump_126 =>
            cases assump_126
            case inl assump_129 =>
              apply Or.inr
              apply True.intro
            case inr assump_130 =>
              apply Or.inr
              apply True.intro
        case inr assump_124 =>
          apply Or.inr
          apply True.intro


variable (p7 p1 p5 p3 p0 p6 p2 : Prop)
theorem file62_88193 : ((((((p2 ∧ p5) → (p1 → False)) → ((True → True) ∧ (p7 → p6))) → (((p3 ∨ p7) → (p0 → False)) → ((p7 ∧ p5) ∨ (p3 → True)))) → False) → False) := by
  intro assump_10
  have assump_24 : ((((p2 ∧ p5) → (p1 → False)) → ((True → True) ∧ (p7 → p6))) → (((p3 ∨ p7) → (p0 → False)) → ((p7 ∧ p5) ∨ (p3 → True)))) := by
    intro assump_14
    intro assump_15
    apply Or.inr
    intro assump_20
    apply True.intro
  let assump_13 := assump_10 assump_24
  apply False.elim assump_13


variable (p2 p4 p7 p6 p3 p0 p5 p1 : Prop)
theorem file62_88734 : (((((True ∨ p1) → False) ∧ ((p3 ∨ p0) ∨ (p2 ∧ False))) → (((p5 → True) → False) ∨ ((p7 ∨ True) → False))) ∧ ((((False → p7) ∧ (p7 ∧ p4)) ∧ ((p7 ∧ p6) → (p6 ∨ p3))) ∨ (((False → p3) → False) → ((p0 ∨ p4) ∨ (p5 ∨ p0))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        have assump_51 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_17 := assump_2 assump_51
        apply False.elim assump_17
      case inr assump_9 =>
        apply Or.inl
        intro assump_23
        have assump_52 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_28 := assump_2 assump_52
        apply False.elim assump_28
    case inr assump_7 =>
      cases assump_7
      case intro assump_32 assump_33 =>
        apply False.elim assump_33
  apply Or.inr
  intro assump_41
  have assump_53 : (False → p3) := by
    intro assump_45
    apply False.elim assump_45
  let assump_44 := assump_41 assump_53
  apply False.elim assump_44


variable (p2 p3 p7 p5 p6 p4 p1 : Prop)
theorem file62_89972 : (((((p3 ∨ p3) → (p6 → p6)) ∨ ((True ∨ p3) → (True ∨ True))) → False) → ((((False → False) ∨ (p4 ∨ p5)) → ((p3 → p2) → (p2 ∨ True))) → (((p1 → False) → (p7 ∧ p7)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_24 : (((p3 ∨ p3) → (p6 → p6)) ∨ ((True ∨ p3) → (True ∨ True))) := by
    apply Or.inl
    intro assump_11
    intro assump_12
    cases assump_11
    case inl assump_15 =>
      exact assump_12
    case inr assump_16 =>
      exact assump_12
  let assump_10 := assump_1 assump_24
  apply False.elim assump_10


variable (p7 p5 p1 p3 p0 p4 : Prop)
theorem file62_90585 : (((((True ∧ p3) → False) ∨ ((p4 → False) → False)) → (((p5 ∧ p5) ∨ (p7 ∧ p7)) → ((True → p5) → False))) → ((((False ∨ False) ∧ (p3 ∧ False)) → ((p7 → p1) → False)) ∨ (((p0 ∨ p4) ∨ (p0 ∨ True)) → ((p3 ∨ True) → (p3 → p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      apply False.elim assump_11


variable (p2 p4 p6 p3 p7 p5 p1 p0 : Prop)
theorem file62_91135 : ((((((p7 ∨ p4) ∨ (p3 ∨ True)) ∨ ((p0 → p5) → False)) ∨ (((p1 → p5) ∨ (p6 ∧ True)) ∧ ((p2 ∨ False) → (p6 → p1)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p7 ∨ p4) ∨ (p3 ∨ True)) ∨ ((p0 → p5) → False)) ∨ (((p1 → p5) ∨ (p6 ∧ True)) ∧ ((p2 ∨ False) → (p6 → p1)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p5 p6 p1 p4 p2 : Prop)
theorem file62_91637 : ((((((p2 ∧ p4) ∨ (p7 → False)) → ((False ∧ p6) → (p5 ∨ p1))) ∨ (((p4 → p4) ∨ (p4 → False)) → False)) → False) → False) := by
  intro assump_5
  have assump_18 : ((((p2 ∧ p4) ∨ (p7 → False)) → ((False ∧ p6) → (p5 ∨ p1))) ∨ (((p4 → p4) ∨ (p4 → False)) → False)) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      apply False.elim assump_11
  let assump_8 := assump_5 assump_18
  apply False.elim assump_8


variable (p6 p1 p7 p0 : Prop)
theorem file62_92169 : (((((False → p7) → False) → False) → False) → ((((True ∨ p0) ∨ (p1 → False)) → False) ∨ (((p1 → False) ∨ (p6 ∧ p0)) → ((True → p0) ∨ (True → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      have assump_59 : (((False → p7) → False) → False) := by
        intro assump_12
        have assump_60 : (False → p7) := by
          intro assump_16
          apply False.elim assump_16
        let assump_15 := assump_12 assump_60
        apply False.elim assump_15
      let assump_11 := assump_1 assump_59
      apply False.elim assump_11
    case inr assump_8 =>
      have assump_61 : (((False → p7) → False) → False) := by
        intro assump_29
        have assump_62 : (False → p7) := by
          intro assump_33
          apply False.elim assump_33
        let assump_32 := assump_29 assump_62
        apply False.elim assump_32
      let assump_28 := assump_1 assump_61
      apply False.elim assump_28
  case inr assump_6 =>
    have assump_63 : (((False → p7) → False) → False) := by
      intro assump_46
      have assump_64 : (False → p7) := by
        intro assump_50
        apply False.elim assump_50
      let assump_49 := assump_46 assump_64
      apply False.elim assump_49
    let assump_45 := assump_1 assump_63
    apply False.elim assump_45


variable (p2 p1 p7 p0 p4 p3 p6 : Prop)
theorem file62_93597 : ((((((p2 → False) → (p1 → p2)) → ((False → p3) ∧ (p4 → p1))) ∨ (((p7 → False) → False) ∨ ((p6 → False) → (True → p0)))) ∧ ((((p2 ∨ p3) ∧ (p6 ∧ p3)) → ((p7 → True) ∨ (p3 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_101 : (((p2 ∨ p3) ∧ (p6 ∧ p3)) → ((p7 → True) ∨ (p3 ∧ p2))) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              apply Or.inl
              intro assump_24
              apply True.intro
          case inr assump_15 =>
            cases assump_13
            case intro assump_27 assump_28 =>
              apply Or.inl
              intro assump_33
              apply True.intro
      let assump_10 := assump_3 assump_101
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_37 =>
        have assump_102 : (((p2 ∨ p3) ∧ (p6 ∧ p3)) → ((p7 → True) ∨ (p3 ∧ p2))) := by
          intro assump_44
          cases assump_44
          case intro assump_45 assump_46 =>
            cases assump_45
            case inl assump_47 =>
              cases assump_46
              case intro assump_51 assump_52 =>
                apply Or.inl
                intro assump_57
                apply True.intro
            case inr assump_48 =>
              cases assump_46
              case intro assump_60 assump_61 =>
                apply Or.inl
                intro assump_66
                apply True.intro
        let assump_43 := assump_3 assump_102
        apply False.elim assump_43
      case inr assump_38 =>
        have assump_103 : (((p2 ∨ p3) ∧ (p6 ∧ p3)) → ((p7 → True) ∨ (p3 ∧ p2))) := by
          intro assump_75
          cases assump_75
          case intro assump_76 assump_77 =>
            cases assump_76
            case inl assump_78 =>
              cases assump_77
              case intro assump_82 assump_83 =>
                apply Or.inl
                intro assump_88
                apply True.intro
            case inr assump_79 =>
              cases assump_77
              case intro assump_91 assump_92 =>
                apply Or.inl
                intro assump_97
                apply True.intro
        let assump_74 := assump_3 assump_103
        apply False.elim assump_74


variable (p7 p4 p3 p0 p5 p6 : Prop)
theorem file62_96141 : (((((p3 ∧ p3) → (p6 ∨ True)) ∨ ((p5 → False) → (True → False))) → False) → ((((p0 ∨ p4) → (True ∧ p6)) ∧ ((p3 → p5) ∨ (p3 ∧ p4))) ∧ (((p4 → False) ∨ (False → p6)) → ((p7 → p7) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  apply And.intro
  apply True.intro
  cases assump_2
  case inl assump_3 =>
    have assump_88 : (((p3 ∧ p3) → (p6 ∨ True)) ∨ ((p5 → False) → (True → False))) := by
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply Or.inr
        apply True.intro
    let assump_9 := assump_1 assump_88
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_89 : (((p3 ∧ p3) → (p6 ∨ True)) ∨ ((p5 → False) → (True → False))) := by
      apply Or.inl
      intro assump_25
      cases assump_25
      case intro assump_26 assump_27 =>
        apply Or.inr
        apply True.intro
    let assump_24 := assump_1 assump_89
    apply False.elim assump_24
  apply Or.inl
  intro assump_37
  have assump_90 : (((p3 ∧ p3) → (p6 ∨ True)) ∨ ((p5 → False) → (True → False))) := by
    apply Or.inl
    intro assump_42
    cases assump_42
    case intro assump_43 assump_44 =>
      apply Or.inr
      apply True.intro
  let assump_41 := assump_1 assump_90
  apply False.elim assump_41
  intro assump_52
  intro assump_53
  cases assump_52
  case inl assump_56 =>
    have assump_91 : (((p3 ∧ p3) → (p6 ∨ True)) ∨ ((p5 → False) → (True → False))) := by
      apply Or.inl
      intro assump_63
      cases assump_63
      case intro assump_64 assump_65 =>
        apply Or.inr
        apply True.intro
    let assump_62 := assump_1 assump_91
    apply False.elim assump_62
  case inr assump_57 =>
    have assump_92 : (((p3 ∧ p3) → (p6 ∨ True)) ∨ ((p5 → False) → (True → False))) := by
      apply Or.inl
      intro assump_78
      cases assump_78
      case intro assump_79 assump_80 =>
        apply Or.inr
        apply True.intro
    let assump_77 := assump_1 assump_92
    apply False.elim assump_77


variable (p7 p0 p5 : Prop)
theorem file62_98216 : (((((False ∨ p5) → (p5 ∨ p0)) → ((False → p7) → False)) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_23 : ((True → False) → False) := by
      intro assump_13
      have assump_24 : True := by
        apply True.intro
      let assump_16 := assump_13 assump_24
      apply False.elim assump_16
    let assump_12 := assump_7 assump_23
    apply False.elim assump_12


variable (p3 p5 p7 p6 : Prop)
theorem file62_98727 : ((((((False ∧ p5) → (p6 ∧ False)) → False) → (((p5 ∨ p5) ∨ (p7 → p3)) → ((p5 → False) ∨ (p3 → p6)))) → False) → False) := by
  intro assump_1
  have assump_77 : ((((False ∧ p5) → (p6 ∧ False)) → False) → (((p5 ∨ p5) ∨ (p7 → p3)) → ((p5 → False) ∨ (p3 → p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        intro assump_15
        have assump_78 : ((False ∧ p5) → (p6 ∧ False)) := by
          intro assump_20
          apply And.intro
          cases assump_20
          case intro assump_21 assump_22 =>
            apply False.elim assump_21
          cases assump_20
          case intro assump_25 assump_26 =>
            apply False.elim assump_25
        let assump_19 := assump_5 assump_78
        apply False.elim assump_19
      case inr assump_10 =>
        apply Or.inl
        intro assump_36
        have assump_79 : ((False ∧ p5) → (p6 ∧ False)) := by
          intro assump_41
          apply And.intro
          cases assump_41
          case intro assump_42 assump_43 =>
            apply False.elim assump_42
          cases assump_41
          case intro assump_46 assump_47 =>
            apply False.elim assump_46
        let assump_40 := assump_5 assump_79
        apply False.elim assump_40
    case inr assump_8 =>
      apply Or.inl
      intro assump_57
      have assump_80 : ((False ∧ p5) → (p6 ∧ False)) := by
        intro assump_62
        apply And.intro
        cases assump_62
        case intro assump_63 assump_64 =>
          apply False.elim assump_63
        cases assump_62
        case intro assump_67 assump_68 =>
          apply False.elim assump_67
      let assump_61 := assump_5 assump_80
      apply False.elim assump_61
  let assump_4 := assump_1 assump_77
  apply False.elim assump_4


variable (p0 p2 p7 : Prop)
theorem file62_100631 : ((((((True → p2) ∧ (p2 ∧ True)) → False) → (((False ∨ False) → False) ∨ ((p2 ∨ p0) ∧ (p2 ∧ p7)))) → ((((p7 ∧ p2) ∧ (False → False)) → False) ∧ (((p0 → False) → (p0 → p7)) → False))) → False) := by
  intro assump_1
  have assump_31 : ((((True → p2) ∧ (p2 ∧ True)) → False) → (((False ∨ False) → False) ∨ ((p2 ∨ p0) ∧ (p2 ∧ p7)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      apply False.elim assump_9
    case inr assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_31
  let assump_15 := And.right assump_4
  have assump_32 : ((p0 → False) → (p0 → p7)) := by
    intro assump_18
    intro assump_19
    have assump_33 : p0 := by
      exact assump_19
    let assump_24 := assump_18 assump_33
    apply False.elim assump_24
  let assump_17 := assump_15 assump_32
  apply False.elim assump_17


variable (p6 p5 p3 p0 p2 p7 p1 p4 : Prop)
theorem file62_101581 : (((((p7 → p6) → (p7 → False)) → ((p2 ∧ p7) ∨ (True ∨ p4))) ∨ (((p7 → False) → (p3 → True)) ∧ ((p6 ∨ p4) → (p6 → p0)))) ∨ ((((p4 → p2) → (True → p6)) → ((p7 → False) → False)) ∨ (((p1 ∧ p5) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p1 p0 p4 p2 p5 : Prop)
theorem file62_101949 : (((((p2 ∧ False) ∧ (p4 ∨ p5)) ∧ ((p1 ∨ True) → False)) ∧ (((p2 → False) → False) → ((p0 ∨ p1) ∧ (p2 ∧ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9


variable (p4 p1 p3 p6 p7 p2 p5 : Prop)
theorem file62_102420 : (((((True ∧ True) → False) → ((p2 ∨ p4) ∨ (p1 ∨ p5))) ∨ (((p6 ∧ p1) ∧ (p5 → False)) → ((p7 → False) ∨ (p2 → False)))) ∨ ((((True → True) ∧ (p3 → p1)) → False) ∨ (((p1 → False) → (False → True)) → ((p6 ∨ p3) ∧ (True → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (True ∧ True) := by
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p4 p1 p3 p6 p2 : Prop)
theorem file62_102925 : ((((((True → False) → (p4 ∧ p2)) ∨ ((p6 → True) → (True ∨ p3))) ∨ (((p1 → p7) → False) → False)) → False) → False) := by
  intro assump_31
  have assump_51 : ((((True → False) → (p4 ∧ p2)) ∨ ((p6 → True) → (True ∨ p3))) ∨ (((p1 → p7) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_35
    apply And.intro
    have assump_52 : True := by
      apply True.intro
    let assump_38 := assump_35 assump_52
    apply False.elim assump_38
    have assump_53 : True := by
      apply True.intro
    let assump_44 := assump_35 assump_53
    apply False.elim assump_44
  let assump_34 := assump_31 assump_51
  apply False.elim assump_34


variable (p7 p2 p0 p3 p1 p6 p5 p4 : Prop)
theorem file62_103646 : (((((p1 → p0) ∧ (p1 → False)) → False) ∨ (((p2 ∨ False) → (p3 ∨ p7)) → ((p0 ∧ p3) ∧ (p6 ∧ p6)))) → ((((p4 ∧ False) ∧ (True ∨ p1)) ∨ ((True → True) ∧ (False → False))) ∨ (((p4 ∧ p7) ∨ (p5 ∧ p6)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    apply And.intro
    intro assump_6
    apply True.intro
    intro assump_7
    apply False.elim assump_7
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    apply And.intro
    intro assump_12
    apply True.intro
    intro assump_13
    apply False.elim assump_13


variable (p2 p0 p7 p6 p1 p5 p3 : Prop)
theorem file62_104289 : (((((p2 → True) ∨ (p5 → p7)) ∧ ((p1 ∧ True) ∨ (p7 → True))) ∧ (((p6 ∨ p0) ∧ (p3 → False)) ∧ ((False ∧ p1) ∧ (p7 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_20
                case inl assump_22 =>
                  cases assump_19
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      apply False.elim assump_30
                case inr assump_23 =>
                  cases assump_19
                  case intro assump_38 assump_39 =>
                    cases assump_38
                    case intro assump_40 assump_41 =>
                      apply False.elim assump_40
        case inr assump_11 =>
          cases assump_3
          case intro assump_46 assump_47 =>
            cases assump_46
            case intro assump_48 assump_49 =>
              cases assump_48
              case inl assump_50 =>
                cases assump_47
                case intro assump_56 assump_57 =>
                  cases assump_56
                  case intro assump_58 assump_59 =>
                    apply False.elim assump_58
              case inr assump_51 =>
                cases assump_47
                case intro assump_66 assump_67 =>
                  cases assump_66
                  case intro assump_68 assump_69 =>
                    apply False.elim assump_68
      case inr assump_7 =>
        cases assump_5
        case inl assump_74 =>
          cases assump_74
          case intro assump_76 assump_77 =>
            cases assump_3
            case intro assump_82 assump_83 =>
              cases assump_82
              case intro assump_84 assump_85 =>
                cases assump_84
                case inl assump_86 =>
                  cases assump_83
                  case intro assump_92 assump_93 =>
                    cases assump_92
                    case intro assump_94 assump_95 =>
                      apply False.elim assump_94
                case inr assump_87 =>
                  cases assump_83
                  case intro assump_102 assump_103 =>
                    cases assump_102
                    case intro assump_104 assump_105 =>
                      apply False.elim assump_104
        case inr assump_75 =>
          cases assump_3
          case intro assump_110 assump_111 =>
            cases assump_110
            case intro assump_112 assump_113 =>
              cases assump_112
              case inl assump_114 =>
                cases assump_111
                case intro assump_120 assump_121 =>
                  cases assump_120
                  case intro assump_122 assump_123 =>
                    apply False.elim assump_122
              case inr assump_115 =>
                cases assump_111
                case intro assump_130 assump_131 =>
                  cases assump_130
                  case intro assump_132 assump_133 =>
                    apply False.elim assump_132


variable (p5 p6 : Prop)
theorem file62_107776 : ((((((True ∧ p6) ∨ (p6 → p5)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((True ∧ p6) ∨ (p6 → p5)) → False) → False) := by
    intro assump_5
    have assump_24 : ((True ∧ p6) ∨ (p6 → p5)) := by
      apply Or.inr
      intro assump_9
      have assump_25 : ((True ∧ p6) ∨ (p6 → p5)) := by
        apply Or.inl
        apply And.intro
        apply True.intro
        exact assump_9
      let assump_13 := assump_5 assump_25
      apply False.elim assump_13
    let assump_8 := assump_5 assump_24
    apply False.elim assump_8
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p2 p5 p1 p7 p6 : Prop)
theorem file62_108465 : ((((((p7 ∨ p3) → (p3 ∧ True)) ∧ ((False → p1) → False)) → (((p6 → False) ∨ (False → False)) ∨ ((p2 ∨ p3) → (p5 ∨ p7)))) → False) → False) := by
  intro assump_109
  have assump_134 : ((((p7 ∨ p3) → (p3 ∧ True)) ∧ ((False → p1) → False)) → (((p6 → False) ∨ (False → False)) ∨ ((p2 ∨ p3) → (p5 ∨ p7)))) := by
    intro assump_113
    cases assump_113
    case intro assump_114 assump_115 =>
      apply Or.inl
      apply Or.inl
      intro assump_120
      have assump_135 : (False → p1) := by
        intro assump_125
        apply False.elim assump_125
      let assump_124 := assump_115 assump_135
      apply False.elim assump_124
  let assump_112 := assump_109 assump_134
  apply False.elim assump_112


variable (p2 p6 p5 p1 p3 : Prop)
theorem file62_109228 : ((((((p1 ∧ p5) ∧ (p2 ∧ p1)) → ((False → False) ∨ (p3 ∧ p6))) ∨ (((p5 ∨ p1) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p1 ∧ p5) ∧ (p2 ∧ p1)) → ((False → False) ∨ (p3 ∧ p6))) ∨ (((p5 ∨ p1) → False) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply Or.inl
          intro assump_20
          apply False.elim assump_20
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p0 p3 p6 : Prop)
theorem file62_109897 : (((((False ∨ p6) → (p3 → p3)) ∨ ((p0 → p0) ∧ (True → False))) → False) → False) := by
  intro assump_1
  have assump_18 : (((False ∨ p6) → (p3 → p3)) ∨ ((p0 → p0) ∧ (True → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      apply False.elim assump_9
    case inr assump_10 =>
      exact assump_6
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p3 p6 p4 p5 p7 p2 : Prop)
theorem file62_110391 : (((((p0 → p0) ∨ (True ∧ p5)) ∨ ((False ∨ p4) ∧ (p0 → False))) ∨ (((p0 → p6) ∨ (p5 → p5)) ∨ ((p6 ∧ p2) ∨ (p4 → False)))) ∨ ((((False → p3) ∧ (True → p0)) ∧ ((p6 → p2) → (p0 ∨ p7))) ∧ (((p4 ∧ p2) → (p0 ∧ p4)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  exact assump_1


variable (p0 p6 p3 p2 p1 : Prop)
theorem file62_110766 : ((((((p2 → p2) → False) → False) ∨ (((p6 ∨ False) → (p0 ∨ p2)) ∨ ((p2 ∧ p1) ∧ (p3 → False)))) → False) → False) := by
  intro assump_6
  have assump_23 : ((((p2 → p2) → False) → False) ∨ (((p6 ∨ False) → (p0 ∨ p2)) ∨ ((p2 ∧ p1) ∧ (p3 → False)))) := by
    apply Or.inl
    intro assump_10
    have assump_24 : (p2 → p2) := by
      intro assump_14
      exact assump_14
    let assump_13 := assump_10 assump_24
    apply False.elim assump_13
  let assump_9 := assump_6 assump_23
  apply False.elim assump_9


variable (p6 p0 p1 p7 : Prop)
theorem file62_111327 : (((((p1 → False) → (False → False)) → False) → False) ∨ ((((p0 → False) ∨ (p7 ∧ p6)) ∧ ((p0 ∧ True) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p1 → False) → (False → False)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p5 p1 p7 p2 : Prop)
theorem file62_111733 : ((((((p2 → True) → False) ∨ ((p1 ∨ p4) → False)) ∧ (((p7 ∧ p2) ∨ (p2 ∨ p5)) → False)) ∧ ((((True → False) → False) ∨ ((False → p1) ∨ (True ∨ p1))) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        have assump_48 : (((True → False) → False) ∨ ((False → p1) ∨ (True ∨ p1))) := by
          apply Or.inl
          intro assump_21
          have assump_49 : True := by
            apply True.intro
          let assump_24 := assump_21 assump_49
          apply False.elim assump_24
        let assump_20 := assump_9 assump_48
        apply False.elim assump_20
      case inr assump_13 =>
        have assump_50 : (((True → False) → False) ∨ ((False → p1) ∨ (True ∨ p1))) := by
          apply Or.inl
          intro assump_38
          have assump_51 : True := by
            apply True.intro
          let assump_41 := assump_38 assump_51
          apply False.elim assump_41
        let assump_37 := assump_9 assump_50
        apply False.elim assump_37


variable (p5 p0 p7 p2 p3 p4 : Prop)
theorem file62_112904 : ((((((p2 → False) ∨ (p5 ∧ p0)) → ((p3 ∨ p4) ∧ (p5 ∨ False))) ∨ (((p4 → p0) → False) ∨ ((p2 → False) ∨ (p7 → False)))) ∧ ((((False → True) ∨ (p3 → p2)) ∨ ((p0 ∧ p3) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_46 : (((False → True) ∨ (p3 → p2)) ∨ ((p0 ∧ p3) → False)) := by
        apply Or.inl
        apply Or.inl
        intro assump_11
        apply True.intro
      let assump_10 := assump_3 assump_46
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_15 =>
        have assump_47 : (((False → True) ∨ (p3 → p2)) ∨ ((p0 ∧ p3) → False)) := by
          apply Or.inl
          apply Or.inl
          intro assump_22
          apply True.intro
        let assump_21 := assump_3 assump_47
        apply False.elim assump_21
      case inr assump_16 =>
        cases assump_16
        case inl assump_26 =>
          have assump_48 : (((False → True) ∨ (p3 → p2)) ∨ ((p0 ∧ p3) → False)) := by
            apply Or.inl
            apply Or.inl
            intro assump_33
            apply True.intro
          let assump_32 := assump_3 assump_48
          apply False.elim assump_32
        case inr assump_27 =>
          have assump_49 : (((False → True) ∨ (p3 → p2)) ∨ ((p0 ∧ p3) → False)) := by
            apply Or.inl
            apply Or.inl
            intro assump_42
            apply True.intro
          let assump_41 := assump_3 assump_49
          apply False.elim assump_41


variable (p3 p4 p7 p2 p5 p0 p6 p1 : Prop)
theorem file62_114529 : (((((False ∧ p5) ∧ (p3 ∧ p4)) → ((p2 ∨ p4) ∧ (p1 → p3))) ∨ (((p0 ∧ p7) → (False → False)) ∨ ((p3 ∧ p0) → (True → False)))) ∨ ((((p5 ∨ p4) → (p4 ∧ p6)) → ((p4 ∧ p4) ∧ (p6 → False))) → (((True → p5) ∧ (False ∧ p6)) ∧ ((p5 ∨ p3) → False)))) := by
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


variable (p4 p6 p2 p7 p5 : Prop)
theorem file62_115195 : ((((((p7 ∧ False) ∧ (p4 ∨ p7)) ∨ ((p6 → p6) ∨ (p2 → p4))) → (((p7 → p5) → False) → ((True ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p7 ∧ False) ∧ (p4 ∨ p7)) ∨ ((p6 → p6) ∨ (p2 → p4))) → (((p7 → p5) → False) → ((True ∧ False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p2 p6 p5 p1 p0 : Prop)
theorem file62_115745 : ((((((p1 → p0) ∨ (True ∨ p1)) → False) → (((p0 ∧ p5) → (p5 ∨ p2)) ∨ ((p5 ∨ p1) ∧ (p6 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 → p0) ∨ (True ∨ p1)) → False) → (((p0 ∧ p5) → (p5 ∨ p2)) ∨ ((p5 ∨ p1) ∧ (p6 ∧ p2)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply Or.inl
      exact assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p7 p4 p1 p3 : Prop)
theorem file62_116271 : (((((p4 ∨ p7) ∨ (False ∨ p4)) ∨ ((p0 ∧ p3) → (p1 → p3))) → False) → False) := by
  intro assump_146
  have assump_163 : (((p4 ∨ p7) ∨ (False ∨ p4)) ∨ ((p0 ∧ p3) → (p1 → p3))) := by
    apply Or.inr
    intro assump_150
    intro assump_151
    cases assump_150
    case intro assump_154 assump_155 =>
      exact assump_155
  let assump_149 := assump_146 assump_163
  apply False.elim assump_149


variable (p1 p3 p0 p4 p7 p2 p6 : Prop)
theorem file62_116730 : (((((p1 → p7) ∧ (p2 → False)) ∧ ((False ∨ p4) ∧ (p2 ∧ True))) ∧ (((p6 ∧ p6) → (p7 ∧ p6)) → False)) → ((((p0 ∨ p1) ∨ (p4 ∨ p1)) ∨ ((p6 → p7) → (p4 ∧ p2))) ∧ (((p2 → False) → (p4 ∨ p1)) ∨ ((p3 ∨ p3) ∨ (p4 ∨ p6))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            apply False.elim assump_14
          case inr assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              apply Or.inl
              apply Or.inr
              apply Or.inl
              exact assump_15
  cases assump_1
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        cases assump_31
        case intro assump_38 assump_39 =>
          cases assump_38
          case inl assump_40 =>
            apply False.elim assump_40
          case inr assump_41 =>
            cases assump_39
            case intro assump_46 assump_47 =>
              apply Or.inl
              intro assump_54
              apply Or.inl
              exact assump_41


variable (p4 p7 p1 p2 p3 p6 : Prop)
theorem file62_118144 : ((((((p3 ∨ p2) → (p6 ∧ True)) ∨ ((p7 → p2) → False)) → (((True → False) → (p1 → False)) ∧ ((p2 → p6) → (False ∨ True)))) ∧ ((((p1 ∧ False) ∨ (False ∧ p7)) ∧ ((p4 ∨ False) → False)) ∧ (((False ∧ True) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13
        case inr assump_11 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply False.elim assump_18


