variable (p7 p6 p0 p3 p2 p5 p4 : Prop)
theorem file13_47 : (((((p7 ∧ True) ∨ (False → False)) ∨ ((True ∨ p3) ∧ (p7 → p5))) ∧ (((p3 ∧ p2) ∨ (p2 → False)) → ((True → False) → (p6 ∧ p7)))) ∨ ((((p0 → p4) ∧ (p7 → False)) ∧ ((p7 → False) → (p7 → p4))) → (((p5 ∨ False) ∧ (p2 → False)) → False))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply False.elim assump_1
  intro assump_4
  intro assump_5
  apply And.intro
  cases assump_4
  case inl assump_8 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      have assump_52 : True := by
        apply True.intro
      let assump_18 := assump_5 assump_52
      apply False.elim assump_18
  case inr assump_9 =>
    have assump_53 : True := by
      apply True.intro
    let assump_25 := assump_5 assump_53
    apply False.elim assump_25
  cases assump_4
  case inl assump_31 =>
    cases assump_31
    case intro assump_33 assump_34 =>
      have assump_54 : True := by
        apply True.intro
      let assump_41 := assump_5 assump_54
      apply False.elim assump_41
  case inr assump_32 =>
    have assump_55 : True := by
      apply True.intro
    let assump_48 := assump_5 assump_55
    apply False.elim assump_48


variable (p2 p7 p1 p4 p5 : Prop)
theorem file13_1265 : ((((((p4 ∧ p1) ∨ (p2 → p5)) ∧ ((p1 → False) ∧ (p4 ∨ p1))) → (((False → False) ∨ (p7 ∧ p1)) ∨ ((p5 → False) ∨ (p5 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_53 : ((((p4 ∧ p1) ∨ (p2 → p5)) ∧ ((p1 → False) ∧ (p4 ∨ p1))) → (((False → False) ∨ (p7 ∧ p1)) ∨ ((p5 → False) ∨ (p5 ∧ p1)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_17
            case inl assump_20 =>
              apply Or.inl
              apply Or.inl
              intro assump_24
              apply False.elim assump_24
            case inr assump_21 =>
              apply Or.inl
              apply Or.inl
              intro assump_29
              apply False.elim assump_29
      case inr assump_9 =>
        cases assump_7
        case intro assump_34 assump_35 =>
          cases assump_35
          case inl assump_38 =>
            apply Or.inl
            apply Or.inl
            intro assump_42
            apply False.elim assump_42
          case inr assump_39 =>
            apply Or.inl
            apply Or.inl
            intro assump_47
            apply False.elim assump_47
  let assump_4 := assump_1 assump_53
  apply False.elim assump_4


variable (p7 p2 p6 p0 p1 p4 p3 : Prop)
theorem file13_2719 : ((((((p3 ∨ p3) → (False ∨ p2)) ∧ ((p7 ∨ p6) → False)) ∧ (((p2 ∧ p1) → False) ∨ ((p0 ∧ False) → (p0 ∧ p7)))) ∧ ((((False ∧ p4) → (False → True)) ∨ ((p7 → p1) → (p1 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case inl assump_12 =>
          have assump_34 : (((False ∧ p4) → (False → True)) ∨ ((p7 → p1) → (p1 ∨ p6))) := by
            apply Or.inl
            intro assump_19
            intro assump_20
            apply True.intro
          let assump_18 := assump_3 assump_34
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_35 : (((False ∧ p4) → (False → True)) ∨ ((p7 → p1) → (p1 ∨ p6))) := by
            apply Or.inl
            intro assump_29
            intro assump_30
            apply True.intro
          let assump_28 := assump_3 assump_35
          apply False.elim assump_28


variable (p3 p5 p1 p2 p6 p4 : Prop)
theorem file13_3812 : (((((p3 ∨ p4) → False) → ((p4 ∨ p5) ∨ (p4 → False))) ∨ (((p6 ∨ p5) → False) ∧ ((p5 → False) ∨ (p2 → False)))) ∨ ((((p4 → True) ∧ (False → p1)) → ((p5 → p6) → False)) ∨ (((p6 ∨ False) → False) ∨ ((True → p3) ∧ (True ∧ p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  have assump_12 : (p3 ∨ p4) := by
    apply Or.inr
    exact assump_4
  let assump_8 := assump_1 assump_12
  apply False.elim assump_8


variable (p7 p6 p4 p3 p5 p0 p2 p1 : Prop)
theorem file13_4324 : (((((p4 ∨ p5) ∧ (True → p3)) → False) ∧ (((True ∨ p3) ∨ (p5 ∧ p5)) → False)) → ((((p2 ∨ p7) → False) ∧ ((p0 → False) ∧ (p3 → p1))) ∨ (((p3 ∧ p6) ∧ (p0 ∨ p4)) ∨ ((True → False) ∧ (p4 → p1))))) := by
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    apply Or.inl
    apply And.intro
    intro assump_37
    cases assump_37
    case inl assump_38 =>
      have assump_70 : ((True ∨ p3) ∨ (p5 ∧ p5)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_43 := assump_32 assump_70
      apply False.elim assump_43
    case inr assump_39 =>
      have assump_71 : ((True ∨ p3) ∨ (p5 ∧ p5)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_50 := assump_32 assump_71
      apply False.elim assump_50
    apply And.intro
    intro assump_54
    have assump_72 : ((True ∨ p3) ∨ (p5 ∧ p5)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_58 := assump_32 assump_72
    apply False.elim assump_58
    intro assump_62
    have assump_73 : ((True ∨ p3) ∨ (p5 ∧ p5)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_66 := assump_32 assump_73
    apply False.elim assump_66


variable (p2 p5 p3 p6 p7 p0 p4 : Prop)
theorem file13_5614 : (((((p4 ∨ p4) ∨ (False ∧ p7)) ∧ ((p4 ∧ False) → False)) ∨ (((p2 → False) ∨ (False ∧ p7)) → ((p5 → p5) ∨ (True → False)))) ∨ ((((p3 → p7) → False) → ((p3 → False) ∨ (True → p4))) ∧ (((p6 → False) → (p7 ∧ p4)) → ((p0 ∨ p6) → False)))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    exact assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_9 assump_10 =>
      apply False.elim assump_9


variable (p0 p4 p6 p1 p3 p5 : Prop)
theorem file13_6166 : ((((((p1 ∨ p3) → (p1 → True)) ∨ ((p4 ∧ p3) ∧ (p5 → p0))) ∧ (((p6 → p6) → (False → False)) ∨ ((p4 ∨ p5) ∧ (p3 ∨ False)))) → False) → False) := by
  intro assump_7
  have assump_20 : ((((p1 ∨ p3) → (p1 → True)) ∨ ((p4 ∧ p3) ∧ (p5 → p0))) ∧ (((p6 → p6) → (False → False)) ∨ ((p4 ∨ p5) ∧ (p3 ∨ False)))) := by
    apply And.intro
    apply Or.inl
    intro assump_11
    intro assump_12
    apply True.intro
    apply Or.inl
    intro assump_13
    intro assump_14
    apply False.elim assump_14
  let assump_10 := assump_7 assump_20
  apply False.elim assump_10


variable (p4 p2 p5 p3 : Prop)
theorem file13_6779 : (((((p5 → p4) → (False → p3)) ∨ ((p3 ∨ p5) → (p2 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p5 → p4) → (False → p3)) ∨ ((p3 ∨ p5) → (p2 ∨ True))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p1 p2 p6 p3 p0 p7 p4 : Prop)
theorem file13_7174 : (((((True → False) ∧ (False ∧ p1)) ∧ ((p4 ∧ p7) ∧ (p6 ∧ p2))) ∧ (((p3 → p0) → (False → p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p2 p0 p7 p6 : Prop)
theorem file13_7629 : ((((((p7 ∨ p0) ∨ (p6 ∧ False)) → ((False ∨ p2) → False)) → False) ∧ ((((p7 → False) → False) → ((False ∧ False) → False)) → False)) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    have assump_41 : (((p7 → False) → False) → ((False ∧ False) → False)) := by
      intro assump_32
      intro assump_33
      cases assump_33
      case intro assump_34 assump_35 =>
        apply False.elim assump_34
    let assump_31 := assump_26 assump_41
    apply False.elim assump_31


variable (p7 p0 p5 p1 : Prop)
theorem file13_8195 : (((((p7 ∧ p7) ∨ (False → False)) ∨ ((True → False) ∨ (p0 → False))) → False) → ((((p7 → False) → False) → ((p0 → p5) ∨ (True ∧ p1))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_14 : (((p7 ∧ p7) ∨ (False → False)) ∨ ((True → False) ∨ (p0 → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p7 p5 p3 p6 p4 p0 p1 : Prop)
theorem file13_8680 : (((((p1 → False) ∨ (p1 → p7)) ∧ ((p6 ∨ True) → False)) → (((p4 → False) ∧ (p6 → False)) → ((p0 → False) → (p4 ∧ p5)))) ∨ ((((p3 ∨ False) ∧ (p0 → False)) ∧ ((True → False) → False)) ∧ (((p5 → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        have assump_60 : (p6 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_20 := assump_13 assump_60
        apply False.elim assump_20
      case inr assump_15 =>
        have assump_61 : (p6 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_28 := assump_13 assump_61
        apply False.elim assump_28
  cases assump_2
  case intro assump_34 assump_35 =>
    cases assump_1
    case intro assump_40 assump_41 =>
      cases assump_40
      case inl assump_42 =>
        have assump_62 : (p6 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_48 := assump_41 assump_62
        apply False.elim assump_48
      case inr assump_43 =>
        have assump_63 : (p6 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_56 := assump_41 assump_63
        apply False.elim assump_56


variable (p4 p6 p0 p7 p3 p5 : Prop)
theorem file13_10114 : (((((p7 ∧ False) → False) ∨ ((p7 ∧ p0) ∨ (p4 → False))) ∧ (((p5 → False) ∨ (True ∨ False)) ∧ ((p3 ∨ True) → False))) → ((((p0 ∧ True) → False) ∨ ((p3 → p5) → False)) → (((p5 ∨ p7) ∧ (True ∨ p5)) → ((p3 → p6) → (p4 ∧ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_8
      case inl assump_13 =>
        cases assump_2
        case inl assump_17 =>
          cases assump_1
          case intro assump_21 assump_22 =>
            cases assump_21
            case inl assump_23 =>
              cases assump_22
              case intro assump_27 assump_28 =>
                cases assump_27
                case inl assump_29 =>
                  have assump_755 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_35 := assump_28 assump_755
                  apply False.elim assump_35
                case inr assump_30 =>
                  cases assump_30
                  case inl assump_39 =>
                    have assump_756 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_45 := assump_28 assump_756
                    apply False.elim assump_45
                  case inr assump_40 =>
                    apply False.elim assump_40
            case inr assump_24 =>
              cases assump_24
              case inl assump_51 =>
                cases assump_51
                case intro assump_53 assump_54 =>
                  cases assump_22
                  case intro assump_59 assump_60 =>
                    cases assump_59
                    case inl assump_61 =>
                      have assump_757 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_67 := assump_60 assump_757
                      apply False.elim assump_67
                    case inr assump_62 =>
                      cases assump_62
                      case inl assump_71 =>
                        have assump_758 : (p3 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_77 := assump_60 assump_758
                        apply False.elim assump_77
                      case inr assump_72 =>
                        apply False.elim assump_72
              case inr assump_52 =>
                cases assump_22
                case intro assump_85 assump_86 =>
                  cases assump_85
                  case inl assump_87 =>
                    have assump_759 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_93 := assump_86 assump_759
                    apply False.elim assump_93
                  case inr assump_88 =>
                    cases assump_88
                    case inl assump_97 =>
                      have assump_760 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_103 := assump_86 assump_760
                      apply False.elim assump_103
                    case inr assump_98 =>
                      apply False.elim assump_98
        case inr assump_18 =>
          cases assump_1
          case intro assump_111 assump_112 =>
            cases assump_111
            case inl assump_113 =>
              cases assump_112
              case intro assump_117 assump_118 =>
                cases assump_117
                case inl assump_119 =>
                  have assump_761 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_125 := assump_118 assump_761
                  apply False.elim assump_125
                case inr assump_120 =>
                  cases assump_120
                  case inl assump_129 =>
                    have assump_762 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_135 := assump_118 assump_762
                    apply False.elim assump_135
                  case inr assump_130 =>
                    apply False.elim assump_130
            case inr assump_114 =>
              cases assump_114
              case inl assump_141 =>
                cases assump_141
                case intro assump_143 assump_144 =>
                  cases assump_112
                  case intro assump_149 assump_150 =>
                    cases assump_149
                    case inl assump_151 =>
                      have assump_763 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_157 := assump_150 assump_763
                      apply False.elim assump_157
                    case inr assump_152 =>
                      cases assump_152
                      case inl assump_161 =>
                        have assump_764 : (p3 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_167 := assump_150 assump_764
                        apply False.elim assump_167
                      case inr assump_162 =>
                        apply False.elim assump_162
              case inr assump_142 =>
                cases assump_112
                case intro assump_175 assump_176 =>
                  cases assump_175
                  case inl assump_177 =>
                    have assump_765 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_183 := assump_176 assump_765
                    apply False.elim assump_183
                  case inr assump_178 =>
                    cases assump_178
                    case inl assump_187 =>
                      have assump_766 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_193 := assump_176 assump_766
                      apply False.elim assump_193
                    case inr assump_188 =>
                      apply False.elim assump_188
      case inr assump_14 =>
        cases assump_2
        case inl assump_201 =>
          cases assump_1
          case intro assump_205 assump_206 =>
            cases assump_205
            case inl assump_207 =>
              cases assump_206
              case intro assump_211 assump_212 =>
                cases assump_211
                case inl assump_213 =>
                  have assump_767 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_219 := assump_212 assump_767
                  apply False.elim assump_219
                case inr assump_214 =>
                  cases assump_214
                  case inl assump_223 =>
                    have assump_768 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_229 := assump_212 assump_768
                    apply False.elim assump_229
                  case inr assump_224 =>
                    apply False.elim assump_224
            case inr assump_208 =>
              cases assump_208
              case inl assump_235 =>
                cases assump_235
                case intro assump_237 assump_238 =>
                  cases assump_206
                  case intro assump_243 assump_244 =>
                    cases assump_243
                    case inl assump_245 =>
                      have assump_769 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_251 := assump_244 assump_769
                      apply False.elim assump_251
                    case inr assump_246 =>
                      cases assump_246
                      case inl assump_255 =>
                        have assump_770 : (p3 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_261 := assump_244 assump_770
                        apply False.elim assump_261
                      case inr assump_256 =>
                        apply False.elim assump_256
              case inr assump_236 =>
                cases assump_206
                case intro assump_269 assump_270 =>
                  cases assump_269
                  case inl assump_271 =>
                    have assump_771 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_277 := assump_270 assump_771
                    apply False.elim assump_277
                  case inr assump_272 =>
                    cases assump_272
                    case inl assump_281 =>
                      have assump_772 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_287 := assump_270 assump_772
                      apply False.elim assump_287
                    case inr assump_282 =>
                      apply False.elim assump_282
        case inr assump_202 =>
          cases assump_1
          case intro assump_295 assump_296 =>
            cases assump_295
            case inl assump_297 =>
              cases assump_296
              case intro assump_301 assump_302 =>
                cases assump_301
                case inl assump_303 =>
                  have assump_773 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_309 := assump_302 assump_773
                  apply False.elim assump_309
                case inr assump_304 =>
                  cases assump_304
                  case inl assump_313 =>
                    have assump_774 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_319 := assump_302 assump_774
                    apply False.elim assump_319
                  case inr assump_314 =>
                    apply False.elim assump_314
            case inr assump_298 =>
              cases assump_298
              case inl assump_325 =>
                cases assump_325
                case intro assump_327 assump_328 =>
                  cases assump_296
                  case intro assump_333 assump_334 =>
                    cases assump_333
                    case inl assump_335 =>
                      have assump_775 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_341 := assump_334 assump_775
                      apply False.elim assump_341
                    case inr assump_336 =>
                      cases assump_336
                      case inl assump_345 =>
                        have assump_776 : (p3 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_351 := assump_334 assump_776
                        apply False.elim assump_351
                      case inr assump_346 =>
                        apply False.elim assump_346
              case inr assump_326 =>
                cases assump_296
                case intro assump_359 assump_360 =>
                  cases assump_359
                  case inl assump_361 =>
                    have assump_777 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_367 := assump_360 assump_777
                    apply False.elim assump_367
                  case inr assump_362 =>
                    cases assump_362
                    case inl assump_371 =>
                      have assump_778 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_377 := assump_360 assump_778
                      apply False.elim assump_377
                    case inr assump_372 =>
                      apply False.elim assump_372
    case inr assump_10 =>
      cases assump_8
      case inl assump_385 =>
        cases assump_2
        case inl assump_389 =>
          cases assump_1
          case intro assump_393 assump_394 =>
            cases assump_393
            case inl assump_395 =>
              cases assump_394
              case intro assump_399 assump_400 =>
                cases assump_399
                case inl assump_401 =>
                  have assump_779 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_407 := assump_400 assump_779
                  apply False.elim assump_407
                case inr assump_402 =>
                  cases assump_402
                  case inl assump_411 =>
                    have assump_780 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_417 := assump_400 assump_780
                    apply False.elim assump_417
                  case inr assump_412 =>
                    apply False.elim assump_412
            case inr assump_396 =>
              cases assump_396
              case inl assump_423 =>
                cases assump_423
                case intro assump_425 assump_426 =>
                  cases assump_394
                  case intro assump_431 assump_432 =>
                    cases assump_431
                    case inl assump_433 =>
                      have assump_781 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_439 := assump_432 assump_781
                      apply False.elim assump_439
                    case inr assump_434 =>
                      cases assump_434
                      case inl assump_443 =>
                        have assump_782 : (p3 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_449 := assump_432 assump_782
                        apply False.elim assump_449
                      case inr assump_444 =>
                        apply False.elim assump_444
              case inr assump_424 =>
                cases assump_394
                case intro assump_457 assump_458 =>
                  cases assump_457
                  case inl assump_459 =>
                    have assump_783 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_465 := assump_458 assump_783
                    apply False.elim assump_465
                  case inr assump_460 =>
                    cases assump_460
                    case inl assump_469 =>
                      have assump_784 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_475 := assump_458 assump_784
                      apply False.elim assump_475
                    case inr assump_470 =>
                      apply False.elim assump_470
        case inr assump_390 =>
          cases assump_1
          case intro assump_483 assump_484 =>
            cases assump_483
            case inl assump_485 =>
              cases assump_484
              case intro assump_489 assump_490 =>
                cases assump_489
                case inl assump_491 =>
                  have assump_785 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_497 := assump_490 assump_785
                  apply False.elim assump_497
                case inr assump_492 =>
                  cases assump_492
                  case inl assump_501 =>
                    have assump_786 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_507 := assump_490 assump_786
                    apply False.elim assump_507
                  case inr assump_502 =>
                    apply False.elim assump_502
            case inr assump_486 =>
              cases assump_486
              case inl assump_513 =>
                cases assump_513
                case intro assump_515 assump_516 =>
                  cases assump_484
                  case intro assump_521 assump_522 =>
                    cases assump_521
                    case inl assump_523 =>
                      have assump_787 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_529 := assump_522 assump_787
                      apply False.elim assump_529
                    case inr assump_524 =>
                      cases assump_524
                      case inl assump_533 =>
                        have assump_788 : (p3 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_539 := assump_522 assump_788
                        apply False.elim assump_539
                      case inr assump_534 =>
                        apply False.elim assump_534
              case inr assump_514 =>
                cases assump_484
                case intro assump_547 assump_548 =>
                  cases assump_547
                  case inl assump_549 =>
                    have assump_789 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_555 := assump_548 assump_789
                    apply False.elim assump_555
                  case inr assump_550 =>
                    cases assump_550
                    case inl assump_559 =>
                      have assump_790 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_565 := assump_548 assump_790
                      apply False.elim assump_565
                    case inr assump_560 =>
                      apply False.elim assump_560
      case inr assump_386 =>
        cases assump_2
        case inl assump_573 =>
          cases assump_1
          case intro assump_577 assump_578 =>
            cases assump_577
            case inl assump_579 =>
              cases assump_578
              case intro assump_583 assump_584 =>
                cases assump_583
                case inl assump_585 =>
                  have assump_791 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_591 := assump_584 assump_791
                  apply False.elim assump_591
                case inr assump_586 =>
                  cases assump_586
                  case inl assump_595 =>
                    have assump_792 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_601 := assump_584 assump_792
                    apply False.elim assump_601
                  case inr assump_596 =>
                    apply False.elim assump_596
            case inr assump_580 =>
              cases assump_580
              case inl assump_607 =>
                cases assump_607
                case intro assump_609 assump_610 =>
                  cases assump_578
                  case intro assump_615 assump_616 =>
                    cases assump_615
                    case inl assump_617 =>
                      have assump_793 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_623 := assump_616 assump_793
                      apply False.elim assump_623
                    case inr assump_618 =>
                      cases assump_618
                      case inl assump_627 =>
                        have assump_794 : (p3 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_633 := assump_616 assump_794
                        apply False.elim assump_633
                      case inr assump_628 =>
                        apply False.elim assump_628
              case inr assump_608 =>
                cases assump_578
                case intro assump_641 assump_642 =>
                  cases assump_641
                  case inl assump_643 =>
                    have assump_795 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_649 := assump_642 assump_795
                    apply False.elim assump_649
                  case inr assump_644 =>
                    cases assump_644
                    case inl assump_653 =>
                      have assump_796 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_659 := assump_642 assump_796
                      apply False.elim assump_659
                    case inr assump_654 =>
                      apply False.elim assump_654
        case inr assump_574 =>
          cases assump_1
          case intro assump_667 assump_668 =>
            cases assump_667
            case inl assump_669 =>
              cases assump_668
              case intro assump_673 assump_674 =>
                cases assump_673
                case inl assump_675 =>
                  have assump_797 : (p3 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_681 := assump_674 assump_797
                  apply False.elim assump_681
                case inr assump_676 =>
                  cases assump_676
                  case inl assump_685 =>
                    have assump_798 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_691 := assump_674 assump_798
                    apply False.elim assump_691
                  case inr assump_686 =>
                    apply False.elim assump_686
            case inr assump_670 =>
              cases assump_670
              case inl assump_697 =>
                cases assump_697
                case intro assump_699 assump_700 =>
                  cases assump_668
                  case intro assump_705 assump_706 =>
                    cases assump_705
                    case inl assump_707 =>
                      have assump_799 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_713 := assump_706 assump_799
                      apply False.elim assump_713
                    case inr assump_708 =>
                      cases assump_708
                      case inl assump_717 =>
                        have assump_800 : (p3 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_723 := assump_706 assump_800
                        apply False.elim assump_723
                      case inr assump_718 =>
                        apply False.elim assump_718
              case inr assump_698 =>
                cases assump_668
                case intro assump_731 assump_732 =>
                  cases assump_731
                  case inl assump_733 =>
                    have assump_801 : (p3 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_739 := assump_732 assump_801
                    apply False.elim assump_739
                  case inr assump_734 =>
                    cases assump_734
                    case inl assump_743 =>
                      have assump_802 : (p3 ∨ True) := by
                        apply Or.inr
                        apply True.intro
                      let assump_749 := assump_732 assump_802
                      apply False.elim assump_749
                    case inr assump_744 =>
                      apply False.elim assump_744
  apply True.intro


variable (p4 p1 p3 p2 p0 : Prop)
theorem file13_34610 : (((((p2 ∧ p0) → (p3 ∨ p0)) ∨ ((p1 → True) ∨ (p4 ∧ True))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p2 ∧ p0) → (p3 ∨ p0)) ∨ ((p1 → True) ∨ (p4 ∧ True))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      exact assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p1 p5 p3 p0 p2 p6 p7 : Prop)
theorem file13_35052 : (((((p0 → False) → False) → ((p7 → p7) ∨ (True → p7))) → False) → ((((p7 → False) ∨ (p2 → p4)) ∨ ((p2 → False) → False)) → (((p5 → p5) → (p1 ∨ p6)) ∧ ((p1 ∨ p3) ∨ (False ∨ p2))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      have assump_98 : (((p0 → False) → False) → ((p7 → p7) ∨ (True → p7))) := by
        intro assump_15
        apply Or.inl
        intro assump_18
        exact assump_18
      let assump_14 := assump_1 assump_98
      apply False.elim assump_14
    case inr assump_9 =>
      have assump_99 : (((p0 → False) → False) → ((p7 → p7) ∨ (True → p7))) := by
        intro assump_29
        apply Or.inl
        intro assump_32
        exact assump_32
      let assump_28 := assump_1 assump_99
      apply False.elim assump_28
  case inr assump_7 =>
    have assump_100 : (((p0 → False) → False) → ((p7 → p7) ∨ (True → p7))) := by
      intro assump_43
      apply Or.inl
      intro assump_46
      exact assump_46
    let assump_42 := assump_1 assump_100
    apply False.elim assump_42
  cases assump_2
  case inl assump_52 =>
    cases assump_52
    case inl assump_54 =>
      have assump_101 : (((p0 → False) → False) → ((p7 → p7) ∨ (True → p7))) := by
        intro assump_61
        apply Or.inl
        intro assump_64
        exact assump_64
      let assump_60 := assump_1 assump_101
      apply False.elim assump_60
    case inr assump_55 =>
      have assump_102 : (((p0 → False) → False) → ((p7 → p7) ∨ (True → p7))) := by
        intro assump_75
        apply Or.inl
        intro assump_78
        exact assump_78
      let assump_74 := assump_1 assump_102
      apply False.elim assump_74
  case inr assump_53 =>
    have assump_103 : (((p0 → False) → False) → ((p7 → p7) ∨ (True → p7))) := by
      intro assump_89
      apply Or.inl
      intro assump_92
      exact assump_92
    let assump_88 := assump_1 assump_103
    apply False.elim assump_88


variable (p1 p6 p5 p4 p7 p3 p0 : Prop)
theorem file13_37119 : (((((p3 → False) ∨ (p1 ∨ p0)) ∨ ((p0 ∧ p1) ∨ (p3 → True))) → False) → ((((p6 → p5) ∧ (False ∧ False)) ∧ ((p6 ∧ p4) ∧ (True ∨ p1))) → (((True ∨ p4) → (True → p3)) → ((p1 ∧ p7) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_2
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_16
        case intro assump_19 assump_20 =>
          apply False.elim assump_19


variable (p4 p1 p3 p0 p5 p7 p6 p2 : Prop)
theorem file13_37719 : (((((p3 ∧ p1) ∨ (p6 ∨ p4)) → False) ∧ (((False → False) ∨ (False → False)) → False)) → ((((False ∧ p7) ∧ (p0 → p2)) ∧ ((p1 ∧ p6) ∧ (False ∧ p6))) → (((p5 ∧ False) → False) ∧ ((p4 ∧ p5) ∧ (p4 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_5
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
  cases assump_2
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        apply False.elim assump_22
  intro assump_26
  cases assump_2
  case intro assump_29 assump_30 =>
    cases assump_29
    case intro assump_31 assump_32 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        apply False.elim assump_33


variable (p5 p1 p7 p4 p0 p6 p3 : Prop)
theorem file13_38820 : (((((p5 ∨ p0) ∨ (p4 → False)) ∧ ((False ∨ True) → False)) ∧ (((p3 ∧ p6) → (p7 → False)) ∧ ((p5 ∨ p4) → False))) → ((((p3 → False) ∨ (p7 → False)) ∧ ((p1 → p4) → (p0 ∧ p7))) ∧ (((p3 ∧ True) ∨ (p0 → p5)) ∧ ((p7 → False) ∨ (True → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            apply Or.inl
            intro assump_20
            have assump_302 : (p5 ∨ p4) := by
              apply Or.inl
              exact assump_8
            let assump_24 := assump_15 assump_302
            apply False.elim assump_24
        case inr assump_9 =>
          cases assump_3
          case intro assump_32 assump_33 =>
            apply Or.inl
            intro assump_38
            have assump_303 : (False ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_44 := assump_5 assump_303
            apply False.elim assump_44
      case inr assump_7 =>
        cases assump_3
        case intro assump_52 assump_53 =>
          apply Or.inl
          intro assump_58
          have assump_304 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_64 := assump_5 assump_304
          apply False.elim assump_64
  intro assump_68
  apply And.intro
  cases assump_1
  case intro assump_71 assump_72 =>
    cases assump_71
    case intro assump_73 assump_74 =>
      cases assump_73
      case inl assump_75 =>
        cases assump_75
        case inl assump_77 =>
          cases assump_72
          case intro assump_83 assump_84 =>
            have assump_305 : (p5 ∨ p4) := by
              apply Or.inl
              exact assump_77
            let assump_89 := assump_84 assump_305
            apply False.elim assump_89
        case inr assump_78 =>
          cases assump_72
          case intro assump_97 assump_98 =>
            exact assump_78
      case inr assump_76 =>
        cases assump_72
        case intro assump_107 assump_108 =>
          have assump_306 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_115 := assump_74 assump_306
          apply False.elim assump_115
  cases assump_1
  case intro assump_121 assump_122 =>
    cases assump_121
    case intro assump_123 assump_124 =>
      cases assump_123
      case inl assump_125 =>
        cases assump_125
        case inl assump_127 =>
          cases assump_122
          case intro assump_133 assump_134 =>
            have assump_307 : (p5 ∨ p4) := by
              apply Or.inl
              exact assump_127
            let assump_139 := assump_134 assump_307
            apply False.elim assump_139
        case inr assump_128 =>
          cases assump_122
          case intro assump_147 assump_148 =>
            have assump_308 : (False ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_155 := assump_124 assump_308
            apply False.elim assump_155
      case inr assump_126 =>
        cases assump_122
        case intro assump_163 assump_164 =>
          have assump_309 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_171 := assump_124 assump_309
          apply False.elim assump_171
  apply And.intro
  cases assump_1
  case intro assump_175 assump_176 =>
    cases assump_175
    case intro assump_177 assump_178 =>
      cases assump_177
      case inl assump_179 =>
        cases assump_179
        case inl assump_181 =>
          cases assump_176
          case intro assump_187 assump_188 =>
            apply Or.inr
            intro assump_193
            exact assump_181
        case inr assump_182 =>
          cases assump_176
          case intro assump_200 assump_201 =>
            apply Or.inr
            intro assump_206
            have assump_310 : (False ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_212 := assump_178 assump_310
            apply False.elim assump_212
      case inr assump_180 =>
        cases assump_176
        case intro assump_220 assump_221 =>
          apply Or.inr
          intro assump_226
          have assump_311 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_232 := assump_178 assump_311
          apply False.elim assump_232
  cases assump_1
  case intro assump_236 assump_237 =>
    cases assump_236
    case intro assump_238 assump_239 =>
      cases assump_238
      case inl assump_240 =>
        cases assump_240
        case inl assump_242 =>
          cases assump_237
          case intro assump_248 assump_249 =>
            apply Or.inl
            intro assump_254
            have assump_312 : (p5 ∨ p4) := by
              apply Or.inl
              exact assump_242
            let assump_258 := assump_249 assump_312
            apply False.elim assump_258
        case inr assump_243 =>
          cases assump_237
          case intro assump_266 assump_267 =>
            apply Or.inl
            intro assump_272
            have assump_313 : (False ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_278 := assump_239 assump_313
            apply False.elim assump_278
      case inr assump_241 =>
        cases assump_237
        case intro assump_286 assump_287 =>
          apply Or.inl
          intro assump_292
          have assump_314 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_298 := assump_239 assump_314
          apply False.elim assump_298


variable (p5 p6 p3 p0 p1 : Prop)
theorem file13_44725 : ((((((True ∧ False) → (p0 ∧ p6)) ∨ ((True → False) → (p5 ∧ p0))) ∧ (((p1 → False) ∧ (p3 → p5)) → ((p3 ∧ True) → (p1 → False)))) → False) → False) := by
  intro assump_31
  have assump_74 : ((((True ∧ False) → (p0 ∧ p6)) ∨ ((True → False) → (p5 ∧ p0))) ∧ (((p1 → False) ∧ (p3 → p5)) → ((p3 ∧ True) → (p1 → False)))) := by
    apply And.intro
    apply Or.inl
    intro assump_35
    apply And.intro
    cases assump_35
    case intro assump_36 assump_37 =>
      apply False.elim assump_37
    cases assump_35
    case intro assump_42 assump_43 =>
      apply False.elim assump_43
    intro assump_48
    intro assump_49
    intro assump_50
    cases assump_49
    case intro assump_53 assump_54 =>
      cases assump_48
      case intro assump_59 assump_60 =>
        have assump_75 : p1 := by
          exact assump_50
        let assump_67 := assump_59 assump_75
        apply False.elim assump_67
  let assump_34 := assump_31 assump_74
  apply False.elim assump_34


variable (p7 p4 p1 p2 p6 : Prop)
theorem file13_45750 : ((((((p4 → p2) → (True ∧ p7)) ∧ ((True → False) ∧ (p1 ∨ p6))) → (((False → p7) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_36 : ((((p4 → p2) → (True ∧ p7)) ∧ ((True → False) ∧ (p1 ∨ p6))) → (((False → p7) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          have assump_37 : True := by
            apply True.intro
          let assump_22 := assump_13 assump_37
          apply False.elim assump_22
        case inr assump_18 =>
          have assump_38 : True := by
            apply True.intro
          let assump_29 := assump_13 assump_38
          apply False.elim assump_29
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p0 p5 : Prop)
theorem file13_46665 : (((((True → False) → False) ∧ ((p0 ∨ True) ∨ (True ∨ p5))) → False) → False) := by
  intro assump_5
  have assump_19 : (((True → False) → False) ∧ ((p0 ∨ True) ∨ (True ∨ p5))) := by
    apply And.intro
    intro assump_9
    have assump_20 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_20
    apply False.elim assump_12
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p4 p7 p0 p2 p1 p5 : Prop)
theorem file13_47192 : (((((p4 → False) → (p2 → p7)) → False) → (((p4 ∨ p1) ∨ (p4 ∧ p4)) ∨ ((p0 ∧ p5) ∨ (p4 → False)))) ∨ ((((p7 ∧ False) ∨ (p2 ∨ False)) ∨ ((True ∧ p4) ∧ (False ∨ p5))) ∧ (((p4 → p1) → (p1 ∨ True)) ∧ ((p7 ∨ p2) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inr
  intro assump_4
  have assump_22 : ((p4 → False) → (p2 → p7)) := by
    intro assump_9
    intro assump_10
    have assump_23 : p4 := by
      exact assump_4
    let assump_15 := assump_9 assump_23
    apply False.elim assump_15
  let assump_8 := assump_1 assump_22
  apply False.elim assump_8


variable (p5 : Prop)
theorem file13_47817 : (((((p5 → p5) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((p5 → p5) → False) → False) := by
    intro assump_5
    have assump_19 : (p5 → p5) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p1 p4 : Prop)
theorem file13_48228 : (((((p1 ∧ p1) ∧ (p4 ∨ p7)) → False) ∧ (((True ∨ False) → (True ∨ p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((True ∨ False) → (True ∨ p1)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        apply True.intro
      case inr assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p2 p3 p6 p1 p7 p5 p4 : Prop)
theorem file13_48760 : (((((False ∨ p6) → (True ∨ p2)) → False) → (((p3 ∨ p1) → False) → ((p4 → False) → (p4 ∧ False)))) ∨ ((((p5 → False) ∨ (p7 ∨ False)) ∨ ((p2 ∧ True) → False)) ∧ (((p3 ∧ False) ∨ (p1 ∨ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  have assump_38 : ((False ∨ p6) → (True ∨ p2)) := by
    intro assump_11
    cases assump_11
    case inl assump_12 =>
      apply False.elim assump_12
    case inr assump_13 =>
      apply Or.inl
      apply True.intro
  let assump_10 := assump_1 assump_38
  apply False.elim assump_10
  have assump_39 : ((False ∨ p6) → (True ∨ p2)) := by
    intro assump_28
    cases assump_28
    case inl assump_29 =>
      apply False.elim assump_29
    case inr assump_30 =>
      apply Or.inl
      apply True.intro
  let assump_27 := assump_1 assump_39
  apply False.elim assump_27


variable (p0 p4 p7 p3 : Prop)
theorem file13_49678 : (((((p0 → False) ∧ (p4 → False)) → ((p4 ∨ p0) → (p7 ∨ p3))) → False) → False) := by
  intro assump_1
  have assump_37 : (((p0 → False) ∧ (p4 → False)) → ((p4 ∨ p0) → (p7 ∨ p3))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        have assump_38 : p4 := by
          exact assump_7
        let assump_17 := assump_12 assump_38
        apply False.elim assump_17
    case inr assump_8 =>
      cases assump_5
      case intro assump_23 assump_24 =>
        have assump_39 : p0 := by
          exact assump_8
        let assump_30 := assump_23 assump_39
        apply False.elim assump_30
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p6 p5 p4 p3 p7 p1 p2 p0 : Prop)
theorem file13_50500 : (((((p4 ∨ p2) ∧ (p2 ∧ p6)) ∨ ((p3 ∧ p7) ∨ (True ∨ p2))) ∨ (((p4 → False) → False) → False)) ∨ ((((p1 → False) ∧ (p0 ∧ p5)) → False) ∧ (((p5 → False) → (p7 → False)) ∧ ((True → p3) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p3 p2 p5 p7 p1 p6 p0 p4 : Prop)
theorem file13_50858 : (((((p7 ∨ p1) ∧ (p4 ∨ p5)) ∧ ((p5 → p2) ∨ (p0 ∧ p4))) → (((p4 ∧ p5) → False) ∧ ((p1 ∨ True) ∧ (p5 ∨ p6)))) → ((((p2 → False) ∨ (p6 → p2)) → ((p2 → False) → (p0 → p3))) → (((p3 ∧ p5) → (p0 ∨ p3)) ∨ ((p7 → False) → (True → True))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply Or.inr
    exact assump_8


variable (p1 p6 p7 p4 p5 p3 : Prop)
theorem file13_51308 : ((((((p4 ∧ p5) → (True ∨ p1)) ∨ ((p3 ∧ p1) ∧ (True → False))) ∧ (((p6 → p1) → (True ∨ p5)) → ((p7 ∧ p5) → (p3 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p4 ∧ p5) → (True ∨ p1)) ∨ ((p3 ∧ p1) ∧ (True → False))) ∧ (((p6 → p1) → (True ∨ p5)) → ((p7 ∧ p5) → (p3 ∨ True)))) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply True.intro
    intro assump_12
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p3 p4 p1 : Prop)
theorem file13_52023 : (((((False → p4) → False) → False) → False) → ((((p3 ∧ True) → False) → ((True ∧ p1) ∧ (p3 ∨ False))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_21 : (((False → p4) → False) → False) := by
    intro assump_8
    have assump_22 : (False → p4) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_8 assump_22
    apply False.elim assump_11
  let assump_7 := assump_1 assump_21
  apply False.elim assump_7


variable (p3 p7 p2 p4 p0 p5 : Prop)
theorem file13_52543 : ((((((True → False) ∧ (p5 ∧ p0)) ∧ ((False → p5) ∧ (p5 → False))) → (((p2 ∨ p2) ∨ (p2 → False)) ∨ ((p3 → p5) → (p0 → p4)))) ∧ ((((p7 → p7) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((p7 → p7) → False) → False) := by
      intro assump_9
      have assump_23 : (p7 → p7) := by
        intro assump_13
        exact assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p0 p3 p1 p5 p2 p4 p7 : Prop)
theorem file13_53165 : (((((p0 → False) → (False → p0)) → False) → (((p7 → False) ∨ (p1 → p3)) ∧ ((p4 ∨ p4) ∨ (p7 ∨ p5)))) ∨ ((((False ∨ p7) ∧ (p7 ∧ p5)) → ((p4 → p7) → (True → False))) ∧ (((p4 ∧ p3) ∨ (p2 → False)) ∨ ((False ∨ p1) → (p5 → p7))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_26 : ((p0 → False) → (False → p0)) := by
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  let assump_8 := assump_1 assump_26
  apply False.elim assump_8
  have assump_27 : ((p0 → False) → (False → p0)) := by
    intro assump_19
    intro assump_20
    apply False.elim assump_20
  let assump_18 := assump_1 assump_27
  apply False.elim assump_18


variable (p4 p0 p3 p6 p5 : Prop)
theorem file13_53918 : (((((p3 ∨ p5) ∨ (p0 ∨ False)) → False) ∧ (((p6 → p0) → (p4 → p4)) → False)) → False) := by
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    have assump_45 : ((p6 → p0) → (p4 → p4)) := by
      intro assump_36
      intro assump_37
      exact assump_37
    let assump_35 := assump_30 assump_45
    apply False.elim assump_35


variable (p0 p2 p3 p5 p4 : Prop)
theorem file13_54327 : (((((True ∨ p5) ∨ (p3 → p0)) → False) → False) ∨ ((((p5 ∨ p4) → (False ∧ p3)) ∧ ((p5 ∨ False) → False)) ∧ (((p2 → p0) ∧ (True → p5)) ∧ ((False → False) ∧ (p4 ∧ p4))))) := by
  apply Or.inl
  intro assump_6
  have assump_13 : ((True ∨ p5) ∨ (p3 → p0)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_9 := assump_6 assump_13
  apply False.elim assump_9


variable (p7 p3 p0 p4 p2 p5 p6 : Prop)
theorem file13_54767 : (((((p7 ∧ p6) ∧ (p6 → False)) → False) → False) → ((((p4 ∧ p5) ∨ (p6 ∧ p6)) ∨ ((p5 ∧ True) → False)) ∨ (((False → p2) → False) ∧ ((p3 → p0) → (p7 → p3))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_31 : (((p7 ∧ p6) ∧ (p6 → False)) → False) := by
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          have assump_32 : p6 := by
            exact assump_17
          let assump_24 := assump_15 assump_32
          apply False.elim assump_24
    let assump_12 := assump_1 assump_31
    apply False.elim assump_12


variable (p5 p7 p2 p3 p6 p0 : Prop)
theorem file13_55537 : (((((False ∧ p5) ∨ (False → p6)) ∨ ((p0 ∨ p3) → (p2 → p7))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False ∧ p5) ∨ (False → p6)) ∨ ((p0 ∨ p3) → (p2 → p7))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p0 p5 p3 p7 p4 : Prop)
theorem file13_55929 : (((((p7 ∧ False) → (False ∨ p0)) → ((False ∧ p5) → (p0 → p5))) → False) → ((((p4 ∨ p3) ∨ (p0 → False)) ∨ ((p0 → False) ∨ (True ∧ p0))) ∧ (((p4 ∨ p6) ∧ (p7 ∨ p6)) → False))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_4
  have assump_102 : (((p7 ∧ False) → (False ∨ p0)) → ((False ∧ p5) → (p0 → p5))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_10
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
  let assump_8 := assump_1 assump_102
  apply False.elim assump_8
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    cases assump_22
    case inl assump_24 =>
      cases assump_23
      case inl assump_28 =>
        have assump_103 : (((p7 ∧ False) → (False ∨ p0)) → ((False ∧ p5) → (p0 → p5))) := by
          intro assump_35
          intro assump_36
          intro assump_37
          cases assump_36
          case intro assump_40 assump_41 =>
            apply False.elim assump_40
        let assump_34 := assump_1 assump_103
        apply False.elim assump_34
      case inr assump_29 =>
        have assump_104 : (((p7 ∧ False) → (False ∨ p0)) → ((False ∧ p5) → (p0 → p5))) := by
          intro assump_52
          intro assump_53
          intro assump_54
          cases assump_53
          case intro assump_57 assump_58 =>
            apply False.elim assump_57
        let assump_51 := assump_1 assump_104
        apply False.elim assump_51
    case inr assump_25 =>
      cases assump_23
      case inl assump_66 =>
        have assump_105 : (((p7 ∧ False) → (False ∨ p0)) → ((False ∧ p5) → (p0 → p5))) := by
          intro assump_73
          intro assump_74
          intro assump_75
          cases assump_74
          case intro assump_78 assump_79 =>
            apply False.elim assump_78
        let assump_72 := assump_1 assump_105
        apply False.elim assump_72
      case inr assump_67 =>
        have assump_106 : (((p7 ∧ False) → (False ∨ p0)) → ((False ∧ p5) → (p0 → p5))) := by
          intro assump_90
          intro assump_91
          intro assump_92
          cases assump_91
          case intro assump_95 assump_96 =>
            apply False.elim assump_95
        let assump_89 := assump_1 assump_106
        apply False.elim assump_89


variable (p3 p0 p2 p1 p6 p4 : Prop)
theorem file13_58293 : (((((False → False) → False) ∧ ((p0 ∨ p3) ∧ (p3 → False))) ∧ (((p0 ∨ p6) ∨ (p4 ∨ True)) ∧ ((False ∨ p6) → (True ∧ p6)))) → ((((p6 ∨ p2) → False) ∨ ((p6 → False) → (p3 ∨ True))) → (((False ∧ True) → False) → ((p1 ∨ True) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_2
    case inl assump_11 =>
      cases assump_1
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          cases assump_18
          case intro assump_21 assump_22 =>
            cases assump_21
            case inl assump_23 =>
              cases assump_16
              case intro assump_29 assump_30 =>
                cases assump_29
                case inl assump_31 =>
                  cases assump_31
                  case inl assump_33 =>
                    have assump_579 : (False → False) := by
                      intro assump_44
                      apply False.elim assump_44
                    let assump_43 := assump_17 assump_579
                    apply False.elim assump_43
                  case inr assump_34 =>
                    have assump_580 : (False → False) := by
                      intro assump_62
                      apply False.elim assump_62
                    let assump_61 := assump_17 assump_580
                    apply False.elim assump_61
                case inr assump_32 =>
                  cases assump_32
                  case inl assump_68 =>
                    have assump_581 : (False → False) := by
                      intro assump_79
                      apply False.elim assump_79
                    let assump_78 := assump_17 assump_581
                    apply False.elim assump_78
                  case inr assump_69 =>
                    have assump_582 : (False → False) := by
                      intro assump_93
                      apply False.elim assump_93
                    let assump_92 := assump_17 assump_582
                    apply False.elim assump_92
            case inr assump_24 =>
              cases assump_16
              case intro assump_103 assump_104 =>
                cases assump_103
                case inl assump_105 =>
                  cases assump_105
                  case inl assump_107 =>
                    have assump_583 : p3 := by
                      exact assump_24
                    let assump_115 := assump_22 assump_583
                    apply False.elim assump_115
                  case inr assump_108 =>
                    have assump_584 : p3 := by
                      exact assump_24
                    let assump_128 := assump_22 assump_584
                    apply False.elim assump_128
                case inr assump_106 =>
                  cases assump_106
                  case inl assump_132 =>
                    have assump_585 : p3 := by
                      exact assump_24
                    let assump_140 := assump_22 assump_585
                    apply False.elim assump_140
                  case inr assump_133 =>
                    have assump_586 : p3 := by
                      exact assump_24
                    let assump_149 := assump_22 assump_586
                    apply False.elim assump_149
    case inr assump_12 =>
      cases assump_1
      case intro assump_155 assump_156 =>
        cases assump_155
        case intro assump_157 assump_158 =>
          cases assump_158
          case intro assump_161 assump_162 =>
            cases assump_161
            case inl assump_163 =>
              cases assump_156
              case intro assump_169 assump_170 =>
                cases assump_169
                case inl assump_171 =>
                  cases assump_171
                  case inl assump_173 =>
                    have assump_587 : (False → False) := by
                      intro assump_184
                      apply False.elim assump_184
                    let assump_183 := assump_157 assump_587
                    apply False.elim assump_183
                  case inr assump_174 =>
                    have assump_588 : (False → False) := by
                      intro assump_202
                      apply False.elim assump_202
                    let assump_201 := assump_157 assump_588
                    apply False.elim assump_201
                case inr assump_172 =>
                  cases assump_172
                  case inl assump_208 =>
                    have assump_589 : (False → False) := by
                      intro assump_219
                      apply False.elim assump_219
                    let assump_218 := assump_157 assump_589
                    apply False.elim assump_218
                  case inr assump_209 =>
                    have assump_590 : (False → False) := by
                      intro assump_233
                      apply False.elim assump_233
                    let assump_232 := assump_157 assump_590
                    apply False.elim assump_232
            case inr assump_164 =>
              cases assump_156
              case intro assump_243 assump_244 =>
                cases assump_243
                case inl assump_245 =>
                  cases assump_245
                  case inl assump_247 =>
                    have assump_591 : p3 := by
                      exact assump_164
                    let assump_255 := assump_162 assump_591
                    apply False.elim assump_255
                  case inr assump_248 =>
                    have assump_592 : p3 := by
                      exact assump_164
                    let assump_268 := assump_162 assump_592
                    apply False.elim assump_268
                case inr assump_246 =>
                  cases assump_246
                  case inl assump_272 =>
                    have assump_593 : p3 := by
                      exact assump_164
                    let assump_280 := assump_162 assump_593
                    apply False.elim assump_280
                  case inr assump_273 =>
                    have assump_594 : p3 := by
                      exact assump_164
                    let assump_289 := assump_162 assump_594
                    apply False.elim assump_289
  case inr assump_6 =>
    cases assump_2
    case inl assump_297 =>
      cases assump_1
      case intro assump_301 assump_302 =>
        cases assump_301
        case intro assump_303 assump_304 =>
          cases assump_304
          case intro assump_307 assump_308 =>
            cases assump_307
            case inl assump_309 =>
              cases assump_302
              case intro assump_315 assump_316 =>
                cases assump_315
                case inl assump_317 =>
                  cases assump_317
                  case inl assump_319 =>
                    have assump_595 : (False → False) := by
                      intro assump_330
                      apply False.elim assump_330
                    let assump_329 := assump_303 assump_595
                    apply False.elim assump_329
                  case inr assump_320 =>
                    have assump_596 : (False → False) := by
                      intro assump_348
                      apply False.elim assump_348
                    let assump_347 := assump_303 assump_596
                    apply False.elim assump_347
                case inr assump_318 =>
                  cases assump_318
                  case inl assump_354 =>
                    have assump_597 : (False → False) := by
                      intro assump_365
                      apply False.elim assump_365
                    let assump_364 := assump_303 assump_597
                    apply False.elim assump_364
                  case inr assump_355 =>
                    have assump_598 : (False → False) := by
                      intro assump_379
                      apply False.elim assump_379
                    let assump_378 := assump_303 assump_598
                    apply False.elim assump_378
            case inr assump_310 =>
              cases assump_302
              case intro assump_389 assump_390 =>
                cases assump_389
                case inl assump_391 =>
                  cases assump_391
                  case inl assump_393 =>
                    have assump_599 : p3 := by
                      exact assump_310
                    let assump_401 := assump_308 assump_599
                    apply False.elim assump_401
                  case inr assump_394 =>
                    have assump_600 : p3 := by
                      exact assump_310
                    let assump_414 := assump_308 assump_600
                    apply False.elim assump_414
                case inr assump_392 =>
                  cases assump_392
                  case inl assump_418 =>
                    have assump_601 : p3 := by
                      exact assump_310
                    let assump_426 := assump_308 assump_601
                    apply False.elim assump_426
                  case inr assump_419 =>
                    have assump_602 : p3 := by
                      exact assump_310
                    let assump_435 := assump_308 assump_602
                    apply False.elim assump_435
    case inr assump_298 =>
      cases assump_1
      case intro assump_441 assump_442 =>
        cases assump_441
        case intro assump_443 assump_444 =>
          cases assump_444
          case intro assump_447 assump_448 =>
            cases assump_447
            case inl assump_449 =>
              cases assump_442
              case intro assump_455 assump_456 =>
                cases assump_455
                case inl assump_457 =>
                  cases assump_457
                  case inl assump_459 =>
                    have assump_603 : (False → False) := by
                      intro assump_470
                      apply False.elim assump_470
                    let assump_469 := assump_443 assump_603
                    apply False.elim assump_469
                  case inr assump_460 =>
                    have assump_604 : (False → False) := by
                      intro assump_488
                      apply False.elim assump_488
                    let assump_487 := assump_443 assump_604
                    apply False.elim assump_487
                case inr assump_458 =>
                  cases assump_458
                  case inl assump_494 =>
                    have assump_605 : (False → False) := by
                      intro assump_505
                      apply False.elim assump_505
                    let assump_504 := assump_443 assump_605
                    apply False.elim assump_504
                  case inr assump_495 =>
                    have assump_606 : (False → False) := by
                      intro assump_519
                      apply False.elim assump_519
                    let assump_518 := assump_443 assump_606
                    apply False.elim assump_518
            case inr assump_450 =>
              cases assump_442
              case intro assump_529 assump_530 =>
                cases assump_529
                case inl assump_531 =>
                  cases assump_531
                  case inl assump_533 =>
                    have assump_607 : p3 := by
                      exact assump_450
                    let assump_541 := assump_448 assump_607
                    apply False.elim assump_541
                  case inr assump_534 =>
                    have assump_608 : p3 := by
                      exact assump_450
                    let assump_554 := assump_448 assump_608
                    apply False.elim assump_554
                case inr assump_532 =>
                  cases assump_532
                  case inl assump_558 =>
                    have assump_609 : p3 := by
                      exact assump_450
                    let assump_566 := assump_448 assump_609
                    apply False.elim assump_566
                  case inr assump_559 =>
                    have assump_610 : p3 := by
                      exact assump_450
                    let assump_575 := assump_448 assump_610
                    apply False.elim assump_575


variable (p5 p1 p6 p7 p3 : Prop)
theorem file13_70651 : (((((p7 ∨ p1) ∨ (p1 → p5)) ∨ ((p5 → p6) ∧ (p6 ∨ p3))) → False) → False) := by
  intro assump_1
  have assump_16 : (((p7 ∨ p1) ∨ (p1 → p5)) ∨ ((p5 → p6) ∧ (p6 ∨ p3))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : (((p7 ∨ p1) ∨ (p1 → p5)) ∨ ((p5 → p6) ∧ (p6 ∨ p3))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p4 p0 p6 p1 p7 p5 p2 : Prop)
theorem file13_71233 : ((((((p0 ∧ p1) ∧ (p4 → p5)) ∨ ((p0 ∨ p7) → (p6 ∧ p0))) → (((p3 → p3) → (p2 ∧ p5)) → False)) ∧ ((((p6 → p1) ∨ (p2 → p4)) → ((p4 → False) → (p4 → False))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_39 : (((p6 → p1) ∨ (p2 → p4)) → ((p4 → False) → (p4 → False))) := by
      intro assump_13
      intro assump_14
      intro assump_15
      cases assump_13
      case inl assump_20 =>
        have assump_40 : p4 := by
          exact assump_15
        let assump_25 := assump_14 assump_40
        apply False.elim assump_25
      case inr assump_21 =>
        have assump_41 : p4 := by
          exact assump_15
        let assump_32 := assump_14 assump_41
        apply False.elim assump_32
    let assump_12 := assump_7 assump_39
    apply False.elim assump_12


variable (p3 p5 p7 p6 p1 : Prop)
theorem file13_72116 : (((((p5 ∨ True) → False) → False) → (((p7 → False) → (p3 → False)) → False)) → ((((p6 → False) ∧ (True ∧ False)) → False) ∨ (((p5 → False) → False) → ((p3 ∨ p1) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply False.elim assump_10


variable (p6 p7 p0 p5 p4 p3 p1 p2 : Prop)
theorem file13_72550 : ((((((p2 ∨ p3) ∧ (p2 ∧ p5)) → False) ∨ (((p4 → True) → False) ∨ ((p1 → False) → False))) ∧ ((((p2 ∧ p4) → (p7 → p2)) → False) ∧ (((p2 ∧ p3) → False) ∧ ((p2 → False) ∨ (p0 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            have assump_167 : ((p2 ∧ p4) → (p7 → p2)) := by
              intro assump_23
              intro assump_24
              cases assump_23
              case intro assump_27 assump_28 =>
                exact assump_27
            let assump_22 := assump_8 assump_167
            apply False.elim assump_22
          case inr assump_17 =>
            cases assump_17
            case intro assump_36 assump_37 =>
              have assump_168 : ((p2 ∧ p4) → (p7 → p2)) := by
                intro assump_46
                intro assump_47
                cases assump_46
                case intro assump_50 assump_51 =>
                  exact assump_50
              let assump_45 := assump_8 assump_168
              apply False.elim assump_45
    case inr assump_5 =>
      cases assump_5
      case inl assump_59 =>
        cases assump_3
        case intro assump_63 assump_64 =>
          cases assump_64
          case intro assump_67 assump_68 =>
            cases assump_68
            case inl assump_71 =>
              have assump_169 : ((p2 ∧ p4) → (p7 → p2)) := by
                intro assump_78
                intro assump_79
                cases assump_78
                case intro assump_82 assump_83 =>
                  exact assump_82
              let assump_77 := assump_63 assump_169
              apply False.elim assump_77
            case inr assump_72 =>
              cases assump_72
              case intro assump_91 assump_92 =>
                have assump_170 : ((p2 ∧ p4) → (p7 → p2)) := by
                  intro assump_101
                  intro assump_102
                  cases assump_101
                  case intro assump_105 assump_106 =>
                    exact assump_105
                let assump_100 := assump_63 assump_170
                apply False.elim assump_100
      case inr assump_60 =>
        cases assump_3
        case intro assump_116 assump_117 =>
          cases assump_117
          case intro assump_120 assump_121 =>
            cases assump_121
            case inl assump_124 =>
              have assump_171 : ((p2 ∧ p4) → (p7 → p2)) := by
                intro assump_131
                intro assump_132
                cases assump_131
                case intro assump_135 assump_136 =>
                  exact assump_135
              let assump_130 := assump_116 assump_171
              apply False.elim assump_130
            case inr assump_125 =>
              cases assump_125
              case intro assump_144 assump_145 =>
                have assump_172 : ((p2 ∧ p4) → (p7 → p2)) := by
                  intro assump_154
                  intro assump_155
                  cases assump_154
                  case intro assump_158 assump_159 =>
                    exact assump_158
                let assump_153 := assump_116 assump_172
                apply False.elim assump_153


variable (p2 p6 p0 p1 p4 p5 p7 : Prop)
theorem file13_75990 : (((((p5 → True) → False) → ((True ∧ p1) → False)) ∧ (((False → False) ∨ (p0 ∨ p5)) ∧ ((p2 ∧ p4) → (True ∨ p1)))) ∨ ((((p5 ∨ p4) → False) ∨ ((False ∧ p7) ∨ (p1 → p4))) ∨ (((p6 → p6) ∧ (p0 → False)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_26 : (p5 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_1 assump_26
    apply False.elim assump_11
  apply And.intro
  apply Or.inl
  intro assump_16
  apply False.elim assump_16
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    apply Or.inl
    apply True.intro


variable (p7 p0 p2 p6 p5 : Prop)
theorem file13_76724 : ((((((p7 → p2) → (p2 → p2)) → ((False → False) ∨ (p0 ∨ p6))) ∧ (((p6 → p6) → False) → ((True → False) ∨ (p5 → False)))) → False) → False) := by
  intro assump_5
  have assump_31 : ((((p7 → p2) → (p2 → p2)) → ((False → False) ∨ (p0 ∨ p6))) ∧ (((p6 → p6) → False) → ((True → False) ∨ (p5 → False)))) := by
    apply And.intro
    intro assump_9
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
    intro assump_15
    apply Or.inl
    intro assump_18
    have assump_32 : (p6 → p6) := by
      intro assump_22
      exact assump_22
    let assump_21 := assump_15 assump_32
    apply False.elim assump_21
  let assump_8 := assump_5 assump_31
  apply False.elim assump_8


variable (p6 p1 p2 p4 p3 : Prop)
theorem file13_77467 : ((((((p1 ∨ True) → False) → ((p4 ∧ p1) → False)) ∧ (((p3 → False) → False) ∨ ((False ∧ p4) ∧ (p6 → False)))) ∧ ((((p1 ∧ p6) ∧ (p2 ∨ p4)) ∨ ((False ∧ p3) ∨ (p6 ∨ True))) → False)) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_18
      case inl assump_21 =>
        have assump_37 : (((p1 ∧ p6) ∧ (p2 ∨ p4)) ∨ ((False ∧ p3) ∨ (p6 ∨ True))) := by
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_27 := assump_16 assump_37
        apply False.elim assump_27
      case inr assump_22 =>
        cases assump_22
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            apply False.elim assump_33


variable (p4 p2 p3 p1 p0 p7 : Prop)
theorem file13_78368 : ((((((p0 → False) ∧ (p3 ∧ p0)) → ((p3 ∧ p4) ∧ (p4 ∧ p7))) ∨ (((p2 ∨ p1) → False) → ((p4 → False) ∨ (p4 → p1)))) → False) → False) := by
  intro assump_1
  have assump_67 : ((((p0 → False) ∧ (p3 ∧ p0)) → ((p3 ∧ p4) ∧ (p4 ∧ p7))) ∨ (((p2 ∨ p1) → False) → ((p4 → False) ∨ (p4 → p1)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        exact assump_10
    cases assump_5
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        have assump_68 : p0 := by
          exact assump_21
        let assump_28 := assump_16 assump_68
        apply False.elim assump_28
    apply And.intro
    cases assump_5
    case intro assump_32 assump_33 =>
      cases assump_33
      case intro assump_36 assump_37 =>
        have assump_69 : p0 := by
          exact assump_37
        let assump_44 := assump_32 assump_69
        apply False.elim assump_44
    cases assump_5
    case intro assump_48 assump_49 =>
      cases assump_49
      case intro assump_52 assump_53 =>
        have assump_70 : p0 := by
          exact assump_53
        let assump_60 := assump_48 assump_70
        apply False.elim assump_60
  let assump_4 := assump_1 assump_67
  apply False.elim assump_4


variable (p1 p6 p2 p0 p5 p4 p7 p3 : Prop)
theorem file13_79800 : (((((p5 ∨ p1) ∨ (p0 → False)) → ((p6 → False) → False)) ∨ (((p0 ∨ p0) ∨ (p4 ∨ p3)) → ((p5 → p1) → False))) → ((((p0 ∨ p5) → False) → ((False ∧ p6) → (p2 → False))) ∨ (((False → p2) → (p7 ∨ p2)) ∧ ((p3 → p6) ∨ (p7 → p6))))) := by
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    apply Or.inl
    intro assump_19
    intro assump_20
    intro assump_21
    cases assump_20
    case intro assump_24 assump_25 =>
      apply False.elim assump_24
  case inr assump_16 =>
    apply Or.inl
    intro assump_30
    intro assump_31
    intro assump_32
    cases assump_31
    case intro assump_35 assump_36 =>
      apply False.elim assump_35


variable (p7 p1 p4 p6 p2 p5 p0 p3 : Prop)
theorem file13_80515 : (((((p0 ∧ p0) → (p2 → p5)) → ((p1 → False) → False)) ∧ (((p6 ∨ p4) → False) ∧ ((p4 → p7) → (p5 → False)))) → ((((p0 ∨ p7) ∧ (False ∧ p3)) ∧ ((p2 → p2) → (p3 ∧ p0))) → False)) := by
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
          apply False.elim assump_11
      case inr assump_8 =>
        cases assump_6
        case intro assump_17 assump_18 =>
          apply False.elim assump_17


variable (p0 p4 p5 p3 p2 p1 p7 p6 : Prop)
theorem file13_81181 : (((((p4 ∧ p5) → (p2 ∨ p2)) ∨ ((p3 ∧ False) ∧ (p3 → p6))) → False) → ((((True → p6) ∧ (p5 → False)) → ((True ∧ p1) ∧ (True ∨ p1))) ∨ (((p7 → p0) ∨ (p7 ∧ p1)) ∨ ((p0 ∨ True) ∨ (True ∧ True))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  apply And.intro
  apply True.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_37 : (((p4 ∧ p5) → (p2 ∨ p2)) ∨ ((p3 ∧ False) ∧ (p3 → p6))) := by
      apply Or.inl
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        have assump_38 : p5 := by
          exact assump_17
        let assump_24 := assump_6 assump_38
        apply False.elim assump_24
    let assump_14 := assump_1 assump_37
    apply False.elim assump_14
  cases assump_4
  case intro assump_31 assump_32 =>
    apply Or.inl
    apply True.intro


variable (p5 p0 p3 p1 p4 p6 p2 : Prop)
theorem file13_82083 : (((((p3 ∨ p2) → False) → ((p3 ∨ p3) → False)) ∨ (((p5 → False) ∧ (p1 ∨ False)) → ((p3 ∧ p1) ∧ (p2 ∧ p0)))) ∨ ((((p0 ∨ p6) ∧ (p4 ∧ p4)) ∨ ((False ∨ True) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_21 : (p3 ∨ p2) := by
      apply Or.inl
      exact assump_3
    let assump_9 := assump_1 assump_21
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_22 : (p3 ∨ p2) := by
      apply Or.inl
      exact assump_4
    let assump_17 := assump_1 assump_22
    apply False.elim assump_17


variable (p4 p1 p5 p2 p0 : Prop)
theorem file13_82740 : (((((p2 ∨ p5) ∨ (False ∨ p4)) → ((p1 ∨ p0) → (True ∨ p1))) → False) → False) := by
  intro assump_1
  have assump_44 : (((p2 ∨ p5) ∨ (False ∨ p4)) → ((p1 ∨ p0) → (True ∨ p1))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          apply True.intro
        case inr assump_14 =>
          apply Or.inl
          apply True.intro
      case inr assump_12 =>
        cases assump_12
        case inl assump_19 =>
          apply False.elim assump_19
        case inr assump_20 =>
          apply Or.inl
          apply True.intro
    case inr assump_8 =>
      cases assump_5
      case inl assump_27 =>
        cases assump_27
        case inl assump_29 =>
          apply Or.inl
          apply True.intro
        case inr assump_30 =>
          apply Or.inl
          apply True.intro
      case inr assump_28 =>
        cases assump_28
        case inl assump_35 =>
          apply False.elim assump_35
        case inr assump_36 =>
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p2 p4 p6 p3 p1 p0 : Prop)
theorem file13_84018 : ((((((p4 ∧ p1) → (p4 ∧ p0)) ∨ ((p0 → p4) ∧ (p0 ∧ True))) → (((p3 ∧ p6) ∨ (True ∧ p2)) ∨ ((p1 → False) → (p1 → p1)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p4 ∧ p1) → (p4 ∧ p0)) ∨ ((p0 → p4) ∧ (p0 ∧ True))) → (((p3 ∧ p6) ∨ (True ∧ p2)) ∨ ((p1 → False) → (p1 → p1)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      intro assump_10
      intro assump_11
      exact assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          apply Or.inr
          intro assump_26
          intro assump_27
          exact assump_27
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p1 p2 p0 p7 p3 p4 p6 : Prop)
theorem file13_84845 : (((((True → p0) → (p7 → False)) ∧ ((p6 ∧ False) ∧ (p3 ∨ False))) ∧ (((p1 ∨ p4) → False) → False)) → ((((p6 → False) → (p3 ∧ p2)) ∧ ((p2 → p4) ∨ (p7 ∨ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              apply False.elim assump_20
    case inr assump_8 =>
      cases assump_8
      case inl assump_25 =>
        cases assump_1
        case intro assump_29 assump_30 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            cases assump_32
            case intro assump_35 assump_36 =>
              cases assump_35
              case intro assump_37 assump_38 =>
                apply False.elim assump_38
      case inr assump_26 =>
        cases assump_1
        case intro assump_45 assump_46 =>
          cases assump_45
          case intro assump_47 assump_48 =>
            cases assump_48
            case intro assump_51 assump_52 =>
              cases assump_51
              case intro assump_53 assump_54 =>
                apply False.elim assump_54


variable (p1 p2 p0 p3 p4 p6 p5 : Prop)
theorem file13_86283 : (((((p4 ∨ p0) → (p3 ∨ p4)) → False) → False) → ((((p3 ∧ False) ∨ (p4 → p0)) → False) → (((p5 → p4) → (False → p6)) ∨ ((p3 ∨ p2) → (p1 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  apply False.elim assump_8


variable (p2 p5 p3 p1 p4 p0 : Prop)
theorem file13_86604 : ((((((p4 → False) ∧ (p3 ∨ p3)) ∧ ((p0 ∨ p1) → (p5 → False))) → False) ∧ ((((p2 → False) → False) → ((False → False) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p2 → False) → False) → ((False → False) → (False → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p4 p6 p3 p5 : Prop)
theorem file13_87144 : ((((((True → p4) → False) → ((p4 → p6) ∧ (True ∨ False))) ∨ (((p5 ∧ p3) ∨ (p3 → True)) → False)) → False) → False) := by
  intro assump_1
  have assump_23 : ((((True → p4) → False) → ((p4 → p6) ∧ (True ∨ False))) ∨ (((p5 ∧ p3) ∨ (p3 → True)) → False)) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_24 : (True → p4) := by
      intro assump_12
      exact assump_6
    let assump_11 := assump_5 assump_24
    apply False.elim assump_11
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p7 p6 p4 p5 : Prop)
theorem file13_87790 : ((((((p7 → False) → (p5 ∨ p6)) ∧ ((True ∨ p3) → False)) → (((p5 ∨ p4) ∨ (True ∨ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_64 : ((((p7 → False) → (p5 ∨ p6)) ∧ ((True ∨ p3) → False)) → (((p5 ∨ p4) ∨ (True ∨ p5)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case intro assump_13 assump_14 =>
          have assump_65 : (True ∨ p3) := by
            apply Or.inl
            apply True.intro
          let assump_19 := assump_14 assump_65
          apply False.elim assump_19
      case inr assump_10 =>
        cases assump_5
        case intro assump_25 assump_26 =>
          have assump_66 : (True ∨ p3) := by
            apply Or.inl
            apply True.intro
          let assump_31 := assump_26 assump_66
          apply False.elim assump_31
    case inr assump_8 =>
      cases assump_8
      case inl assump_35 =>
        cases assump_5
        case intro assump_39 assump_40 =>
          have assump_67 : (True ∨ p3) := by
            apply Or.inl
            apply True.intro
          let assump_45 := assump_40 assump_67
          apply False.elim assump_45
      case inr assump_36 =>
        cases assump_5
        case intro assump_51 assump_52 =>
          have assump_68 : (True ∨ p3) := by
            apply Or.inl
            apply True.intro
          let assump_57 := assump_52 assump_68
          apply False.elim assump_57
  let assump_4 := assump_1 assump_64
  apply False.elim assump_4


variable (p3 p2 p5 p0 p4 p6 : Prop)
theorem file13_89421 : ((((((p5 → p0) → False) ∧ ((p3 ∨ p3) ∨ (p4 → p6))) → (((p2 ∧ p3) ∨ (p4 ∧ True)) ∨ ((p6 ∨ True) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p5 → p0) → False) ∧ ((p3 ∨ p3) ∨ (p4 → p6))) → (((p2 ∧ p3) ∨ (p4 ∧ True)) ∨ ((p6 ∨ True) ∨ (False → False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inr
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_13 =>
          apply Or.inr
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_11 =>
        apply Or.inr
        apply Or.inl
        apply Or.inr
        apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p7 p4 p3 p2 p6 p5 : Prop)
theorem file13_90357 : (((((p2 ∧ p4) ∨ (True → True)) ∨ ((True → False) ∧ (True ∧ p4))) → False) → ((((p3 ∨ p5) ∨ (p7 → p5)) → ((p6 ∧ p5) ∨ (True → False))) → (((False ∨ p4) ∧ (p6 ∨ p2)) → ((p2 ∨ p6) → (False → False))))) := by
  intro assump_9
  intro assump_10
  intro assump_11
  intro assump_12
  intro assump_13
  apply False.elim assump_13


variable (p6 p3 p4 p1 p5 p2 : Prop)
theorem file13_90740 : (((((p6 → p4) → False) → ((p4 → False) ∨ (True → p3))) ∧ (((p1 → False) ∧ (True → False)) → False)) ∨ ((((p5 ∨ p4) ∨ (p6 → False)) ∧ ((p1 ∧ p2) ∨ (p3 ∧ p5))) ∧ (((p4 → False) → (p2 ∧ True)) ∧ ((p5 → p2) ∨ (p1 ∨ p6))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_26 : (p6 → p4) := by
    intro assump_9
    exact assump_4
  let assump_8 := assump_1 assump_26
  apply False.elim assump_8
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    have assump_27 : True := by
      apply True.intro
    let assump_22 := assump_17 assump_27
    apply False.elim assump_22


variable (p6 p3 p5 p0 p4 p2 : Prop)
theorem file13_91444 : (((((False ∧ p2) ∧ (p4 → False)) ∧ ((p6 ∨ p2) → False)) ∧ (((p3 ∧ p0) ∨ (p5 → False)) ∧ ((p4 ∧ False) → False))) → False) := by
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


variable (p5 p4 p3 p2 p1 p7 : Prop)
theorem file13_91913 : (((((p7 → False) → False) ∨ ((p1 ∨ p3) → (p1 → p7))) ∧ (((p4 → p7) ∨ (p2 → False)) ∧ ((False ∧ p5) ∧ (p4 → False)))) → False) := by
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
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
        case inr assump_11 =>
          cases assump_9
          case intro assump_22 assump_23 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              apply False.elim assump_24
    case inr assump_5 =>
      cases assump_3
      case intro assump_30 assump_31 =>
        cases assump_30
        case inl assump_32 =>
          cases assump_31
          case intro assump_36 assump_37 =>
            cases assump_36
            case intro assump_38 assump_39 =>
              apply False.elim assump_38
        case inr assump_33 =>
          cases assump_31
          case intro assump_44 assump_45 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              apply False.elim assump_46


variable (p1 p6 p5 p4 p7 p3 p2 p0 : Prop)
theorem file13_93273 : (((((p1 ∨ True) → (True ∨ p1)) → False) ∧ (((p4 ∨ p6) → False) ∨ ((p0 ∨ p7) ∨ (p5 → False)))) → ((((p6 → p0) ∧ (False → p3)) ∧ ((False → p4) → (p2 ∨ p0))) ∧ (((p1 ∧ p4) ∨ (p1 → False)) ∧ ((p3 → False) ∧ (p1 ∨ p2))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      have assump_328 : (p4 ∨ p6) := by
        apply Or.inr
        exact assump_2
      let assump_13 := assump_9 assump_328
      apply False.elim assump_13
    case inr assump_10 =>
      cases assump_10
      case inl assump_17 =>
        cases assump_17
        case inl assump_19 =>
          exact assump_19
        case inr assump_20 =>
          have assump_329 : ((p1 ∨ True) → (True ∨ p1)) := by
            intro assump_27
            cases assump_27
            case inl assump_28 =>
              apply Or.inl
              apply True.intro
            case inr assump_29 =>
              apply Or.inl
              apply True.intro
          let assump_26 := assump_5 assump_329
          apply False.elim assump_26
      case inr assump_18 =>
        have assump_330 : ((p1 ∨ True) → (True ∨ p1)) := by
          intro assump_41
          cases assump_41
          case inl assump_42 =>
            apply Or.inl
            apply True.intro
          case inr assump_43 =>
            apply Or.inl
            apply True.intro
        let assump_40 := assump_5 assump_330
        apply False.elim assump_40
  intro assump_51
  apply False.elim assump_51
  intro assump_54
  cases assump_1
  case intro assump_57 assump_58 =>
    cases assump_58
    case inl assump_61 =>
      have assump_331 : ((p1 ∨ True) → (True ∨ p1)) := by
        intro assump_67
        cases assump_67
        case inl assump_68 =>
          apply Or.inl
          apply True.intro
        case inr assump_69 =>
          apply Or.inl
          apply True.intro
      let assump_66 := assump_57 assump_331
      apply False.elim assump_66
    case inr assump_62 =>
      cases assump_62
      case inl assump_77 =>
        cases assump_77
        case inl assump_79 =>
          apply Or.inr
          exact assump_79
        case inr assump_80 =>
          have assump_332 : ((p1 ∨ True) → (True ∨ p1)) := by
            intro assump_87
            cases assump_87
            case inl assump_88 =>
              apply Or.inl
              apply True.intro
            case inr assump_89 =>
              apply Or.inl
              apply True.intro
          let assump_86 := assump_57 assump_332
          apply False.elim assump_86
      case inr assump_78 =>
        have assump_333 : ((p1 ∨ True) → (True ∨ p1)) := by
          intro assump_101
          cases assump_101
          case inl assump_102 =>
            apply Or.inl
            apply True.intro
          case inr assump_103 =>
            apply Or.inl
            apply True.intro
        let assump_100 := assump_57 assump_333
        apply False.elim assump_100
  apply And.intro
  cases assump_1
  case intro assump_111 assump_112 =>
    cases assump_112
    case inl assump_115 =>
      apply Or.inr
      intro assump_119
      have assump_334 : ((p1 ∨ True) → (True ∨ p1)) := by
        intro assump_125
        cases assump_125
        case inl assump_126 =>
          apply Or.inl
          apply True.intro
        case inr assump_127 =>
          apply Or.inl
          apply True.intro
      let assump_124 := assump_111 assump_334
      apply False.elim assump_124
    case inr assump_116 =>
      cases assump_116
      case inl assump_135 =>
        cases assump_135
        case inl assump_137 =>
          apply Or.inr
          intro assump_141
          have assump_335 : ((p1 ∨ True) → (True ∨ p1)) := by
            intro assump_147
            cases assump_147
            case inl assump_148 =>
              apply Or.inl
              apply True.intro
            case inr assump_149 =>
              apply Or.inl
              apply True.intro
          let assump_146 := assump_111 assump_335
          apply False.elim assump_146
        case inr assump_138 =>
          apply Or.inr
          intro assump_159
          have assump_336 : ((p1 ∨ True) → (True ∨ p1)) := by
            intro assump_165
            cases assump_165
            case inl assump_166 =>
              apply Or.inl
              apply True.intro
            case inr assump_167 =>
              apply Or.inl
              apply True.intro
          let assump_164 := assump_111 assump_336
          apply False.elim assump_164
      case inr assump_136 =>
        apply Or.inr
        intro assump_177
        have assump_337 : ((p1 ∨ True) → (True ∨ p1)) := by
          intro assump_183
          cases assump_183
          case inl assump_184 =>
            apply Or.inl
            apply True.intro
          case inr assump_185 =>
            apply Or.inl
            apply True.intro
        let assump_182 := assump_111 assump_337
        apply False.elim assump_182
  apply And.intro
  intro assump_193
  cases assump_1
  case intro assump_196 assump_197 =>
    cases assump_197
    case inl assump_200 =>
      have assump_338 : ((p1 ∨ True) → (True ∨ p1)) := by
        intro assump_206
        cases assump_206
        case inl assump_207 =>
          apply Or.inl
          apply True.intro
        case inr assump_208 =>
          apply Or.inl
          apply True.intro
      let assump_205 := assump_196 assump_338
      apply False.elim assump_205
    case inr assump_201 =>
      cases assump_201
      case inl assump_216 =>
        cases assump_216
        case inl assump_218 =>
          have assump_339 : ((p1 ∨ True) → (True ∨ p1)) := by
            intro assump_224
            cases assump_224
            case inl assump_225 =>
              apply Or.inl
              apply True.intro
            case inr assump_226 =>
              apply Or.inl
              apply True.intro
          let assump_223 := assump_196 assump_339
          apply False.elim assump_223
        case inr assump_219 =>
          have assump_340 : ((p1 ∨ True) → (True ∨ p1)) := by
            intro assump_238
            cases assump_238
            case inl assump_239 =>
              apply Or.inl
              apply True.intro
            case inr assump_240 =>
              apply Or.inl
              apply True.intro
          let assump_237 := assump_196 assump_340
          apply False.elim assump_237
      case inr assump_217 =>
        have assump_341 : ((p1 ∨ True) → (True ∨ p1)) := by
          intro assump_252
          cases assump_252
          case inl assump_253 =>
            apply Or.inl
            apply True.intro
          case inr assump_254 =>
            apply Or.inl
            apply True.intro
        let assump_251 := assump_196 assump_341
        apply False.elim assump_251
  cases assump_1
  case intro assump_262 assump_263 =>
    cases assump_263
    case inl assump_266 =>
      have assump_342 : ((p1 ∨ True) → (True ∨ p1)) := by
        intro assump_272
        cases assump_272
        case inl assump_273 =>
          apply Or.inl
          apply True.intro
        case inr assump_274 =>
          apply Or.inl
          apply True.intro
      let assump_271 := assump_262 assump_342
      apply False.elim assump_271
    case inr assump_267 =>
      cases assump_267
      case inl assump_282 =>
        cases assump_282
        case inl assump_284 =>
          have assump_343 : ((p1 ∨ True) → (True ∨ p1)) := by
            intro assump_290
            cases assump_290
            case inl assump_291 =>
              apply Or.inl
              apply True.intro
            case inr assump_292 =>
              apply Or.inl
              apply True.intro
          let assump_289 := assump_262 assump_343
          apply False.elim assump_289
        case inr assump_285 =>
          have assump_344 : ((p1 ∨ True) → (True ∨ p1)) := by
            intro assump_304
            cases assump_304
            case inl assump_305 =>
              apply Or.inl
              apply True.intro
            case inr assump_306 =>
              apply Or.inl
              apply True.intro
          let assump_303 := assump_262 assump_344
          apply False.elim assump_303
      case inr assump_283 =>
        have assump_345 : ((p1 ∨ True) → (True ∨ p1)) := by
          intro assump_318
          cases assump_318
          case inl assump_319 =>
            apply Or.inl
            apply True.intro
          case inr assump_320 =>
            apply Or.inl
            apply True.intro
        let assump_317 := assump_262 assump_345
        apply False.elim assump_317


variable (p0 p3 p2 p6 p5 p4 : Prop)
theorem file13_102032 : ((((((p3 ∨ True) → (True → False)) → ((p5 → p2) ∧ (p6 ∧ p5))) ∨ (((p2 → p2) ∨ (True → p3)) → False)) ∧ ((((p5 ∧ p6) → (False ∨ p2)) ∨ ((p0 → False) ∧ (p0 ∨ True))) ∧ (((p4 → p2) ∧ (p3 → False)) ∧ ((False → p4) → False)))) → False) := by
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case inl assump_19 =>
      cases assump_18
      case intro assump_23 assump_24 =>
        cases assump_23
        case inl assump_25 =>
          cases assump_24
          case intro assump_29 assump_30 =>
            cases assump_29
            case intro assump_31 assump_32 =>
              have assump_159 : (False → p4) := by
                intro assump_40
                apply False.elim assump_40
              let assump_39 := assump_30 assump_159
              apply False.elim assump_39
        case inr assump_26 =>
          cases assump_26
          case intro assump_46 assump_47 =>
            cases assump_47
            case inl assump_50 =>
              cases assump_24
              case intro assump_54 assump_55 =>
                cases assump_54
                case intro assump_56 assump_57 =>
                  have assump_160 : (False → p4) := by
                    intro assump_65
                    apply False.elim assump_65
                  let assump_64 := assump_55 assump_160
                  apply False.elim assump_64
            case inr assump_51 =>
              cases assump_24
              case intro assump_73 assump_74 =>
                cases assump_73
                case intro assump_75 assump_76 =>
                  have assump_161 : (False → p4) := by
                    intro assump_84
                    apply False.elim assump_84
                  let assump_83 := assump_74 assump_161
                  apply False.elim assump_83
    case inr assump_20 =>
      cases assump_18
      case intro assump_92 assump_93 =>
        cases assump_92
        case inl assump_94 =>
          cases assump_93
          case intro assump_98 assump_99 =>
            cases assump_98
            case intro assump_100 assump_101 =>
              have assump_162 : (False → p4) := by
                intro assump_109
                apply False.elim assump_109
              let assump_108 := assump_99 assump_162
              apply False.elim assump_108
        case inr assump_95 =>
          cases assump_95
          case intro assump_115 assump_116 =>
            cases assump_116
            case inl assump_119 =>
              cases assump_93
              case intro assump_123 assump_124 =>
                cases assump_123
                case intro assump_125 assump_126 =>
                  have assump_163 : (False → p4) := by
                    intro assump_134
                    apply False.elim assump_134
                  let assump_133 := assump_124 assump_163
                  apply False.elim assump_133
            case inr assump_120 =>
              cases assump_93
              case intro assump_142 assump_143 =>
                cases assump_142
                case intro assump_144 assump_145 =>
                  have assump_164 : (False → p4) := by
                    intro assump_153
                    apply False.elim assump_153
                  let assump_152 := assump_143 assump_164
                  apply False.elim assump_152


variable (p5 p2 p0 p3 p1 : Prop)
theorem file13_105447 : (((((False → False) → False) → False) ∨ (((p5 → p1) → False) ∨ ((p0 → False) → (p0 ∨ False)))) ∨ ((((p2 ∨ p3) ∨ (p1 → False)) → ((p3 → p2) → False)) → (((True ∨ p0) → False) ∨ ((p5 ∨ False) → (True ∨ p3))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → False) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p5 p2 p6 p3 : Prop)
theorem file13_105920 : (((((p6 ∨ p4) → (False → False)) ∨ ((True ∨ False) → False)) → False) → ((((p6 → p3) → False) ∧ ((p3 → p2) → False)) ∨ (((p5 ∨ p5) ∨ (p3 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_28 : (((p6 ∨ p4) → (False → False)) ∨ ((True ∨ False) → False)) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  let assump_8 := assump_1 assump_28
  apply False.elim assump_8
  intro assump_16
  have assump_29 : (((p6 ∨ p4) → (False → False)) ∨ ((True ∨ False) → False)) := by
    apply Or.inl
    intro assump_21
    intro assump_22
    apply False.elim assump_22
  let assump_20 := assump_1 assump_29
  apply False.elim assump_20


variable (p6 p3 p7 p1 p5 : Prop)
theorem file13_106701 : ((((((False → p1) → False) → False) ∨ (((False ∨ p7) ∧ (p6 → True)) → ((p5 → False) → (True ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → p1) → False) → False) ∨ (((False ∨ p7) ∧ (p6 → True)) → ((p5 → False) → (True ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → p1) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p2 p0 p1 p5 p6 p7 : Prop)
theorem file13_107293 : ((((((p7 → False) → False) ∧ ((p2 → p6) ∨ (p5 ∧ p4))) ∨ (((p0 → p5) → False) ∧ ((p0 ∨ False) ∨ (p6 → False)))) ∧ ((((p0 → p1) ∨ (p7 ∨ False)) ∧ ((False ∧ False) → False)) ∧ (((p0 ∨ p7) → False) ∧ ((p4 ∧ p6) ∧ (p7 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_15
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      cases assump_29
                      case intro assump_36 assump_37 =>
                        apply False.elim assump_37
              case inr assump_19 =>
                cases assump_19
                case inl assump_42 =>
                  cases assump_15
                  case intro assump_48 assump_49 =>
                    cases assump_49
                    case intro assump_52 assump_53 =>
                      cases assump_52
                      case intro assump_54 assump_55 =>
                        cases assump_53
                        case intro assump_60 assump_61 =>
                          apply False.elim assump_61
                case inr assump_43 =>
                  apply False.elim assump_43
        case inr assump_11 =>
          cases assump_11
          case intro assump_68 assump_69 =>
            cases assump_3
            case intro assump_74 assump_75 =>
              cases assump_74
              case intro assump_76 assump_77 =>
                cases assump_76
                case inl assump_78 =>
                  cases assump_75
                  case intro assump_84 assump_85 =>
                    cases assump_85
                    case intro assump_88 assump_89 =>
                      cases assump_88
                      case intro assump_90 assump_91 =>
                        cases assump_89
                        case intro assump_96 assump_97 =>
                          apply False.elim assump_97
                case inr assump_79 =>
                  cases assump_79
                  case inl assump_102 =>
                    cases assump_75
                    case intro assump_108 assump_109 =>
                      cases assump_109
                      case intro assump_112 assump_113 =>
                        cases assump_112
                        case intro assump_114 assump_115 =>
                          cases assump_113
                          case intro assump_120 assump_121 =>
                            apply False.elim assump_121
                  case inr assump_103 =>
                    apply False.elim assump_103
    case inr assump_5 =>
      cases assump_5
      case intro assump_128 assump_129 =>
        cases assump_129
        case inl assump_132 =>
          cases assump_132
          case inl assump_134 =>
            cases assump_3
            case intro assump_138 assump_139 =>
              cases assump_138
              case intro assump_140 assump_141 =>
                cases assump_140
                case inl assump_142 =>
                  cases assump_139
                  case intro assump_148 assump_149 =>
                    cases assump_149
                    case intro assump_152 assump_153 =>
                      cases assump_152
                      case intro assump_154 assump_155 =>
                        cases assump_153
                        case intro assump_160 assump_161 =>
                          apply False.elim assump_161
                case inr assump_143 =>
                  cases assump_143
                  case inl assump_166 =>
                    cases assump_139
                    case intro assump_172 assump_173 =>
                      cases assump_173
                      case intro assump_176 assump_177 =>
                        cases assump_176
                        case intro assump_178 assump_179 =>
                          cases assump_177
                          case intro assump_184 assump_185 =>
                            apply False.elim assump_185
                  case inr assump_167 =>
                    apply False.elim assump_167
          case inr assump_135 =>
            apply False.elim assump_135
        case inr assump_133 =>
          cases assump_3
          case intro assump_196 assump_197 =>
            cases assump_196
            case intro assump_198 assump_199 =>
              cases assump_198
              case inl assump_200 =>
                cases assump_197
                case intro assump_206 assump_207 =>
                  cases assump_207
                  case intro assump_210 assump_211 =>
                    cases assump_210
                    case intro assump_212 assump_213 =>
                      cases assump_211
                      case intro assump_218 assump_219 =>
                        apply False.elim assump_219
              case inr assump_201 =>
                cases assump_201
                case inl assump_224 =>
                  cases assump_197
                  case intro assump_230 assump_231 =>
                    cases assump_231
                    case intro assump_234 assump_235 =>
                      cases assump_234
                      case intro assump_236 assump_237 =>
                        cases assump_235
                        case intro assump_242 assump_243 =>
                          apply False.elim assump_243
                case inr assump_225 =>
                  apply False.elim assump_225


variable (p4 p1 p6 p0 : Prop)
theorem file13_113315 : (((((True → False) → (False ∧ p4)) ∨ ((p6 ∧ p1) ∨ (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_21 : (((True → False) → (False ∧ p4)) ∨ ((p6 ∧ p1) ∨ (p0 → False))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    have assump_22 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_22
    apply False.elim assump_8
    have assump_23 : True := by
      apply True.intro
    let assump_14 := assump_5 assump_23
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p3 p4 p0 p5 p2 : Prop)
theorem file13_113937 : ((((((False → False) ∨ (p5 → p5)) ∨ ((p5 ∧ p0) ∨ (True ∧ p2))) ∨ (((p2 ∨ p4) → False) ∨ ((p0 ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) ∨ (p5 → p5)) ∨ ((p5 ∧ p0) ∨ (True ∧ p2))) ∨ (((p2 ∨ p4) → False) ∨ ((p0 ∧ p3) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p2 p7 p0 p1 p5 p3 : Prop)
theorem file13_114449 : (((((p4 ∨ False) → (True ∨ p5)) → ((p3 ∧ p4) ∧ (p1 → p1))) ∨ (((p0 → p1) ∧ (p7 → False)) ∨ ((p5 → p4) ∨ (p1 ∧ p1)))) → ((((p5 → True) → False) → ((p0 → False) ∨ (p1 ∨ p5))) ∨ (((p3 ∨ p4) ∧ (p2 → True)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply Or.inl
    intro assump_9
    have assump_72 : (p5 → True) := by
      intro assump_14
      apply True.intro
    let assump_13 := assump_6 assump_72
    apply False.elim assump_13
  case inr assump_3 =>
    cases assump_3
    case inl assump_18 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply Or.inl
        intro assump_26
        apply Or.inl
        intro assump_29
        have assump_73 : (p5 → True) := by
          intro assump_34
          apply True.intro
        let assump_33 := assump_26 assump_73
        apply False.elim assump_33
    case inr assump_19 =>
      cases assump_19
      case inl assump_38 =>
        apply Or.inl
        intro assump_42
        apply Or.inl
        intro assump_45
        have assump_74 : (p5 → True) := by
          intro assump_50
          apply True.intro
        let assump_49 := assump_42 assump_74
        apply False.elim assump_49
      case inr assump_39 =>
        cases assump_39
        case intro assump_54 assump_55 =>
          apply Or.inl
          intro assump_60
          apply Or.inl
          intro assump_63
          have assump_75 : (p5 → True) := by
            intro assump_68
            apply True.intro
          let assump_67 := assump_60 assump_75
          apply False.elim assump_67


variable (p0 p7 p3 p4 p6 p2 : Prop)
theorem file13_116128 : (((((False → False) ∨ (False → True)) ∨ ((False ∧ p6) → (p6 ∨ p3))) → False) → ((((p4 ∧ p7) → False) → ((p2 ∧ p3) → (p3 ∧ p4))) ∧ (((p2 ∧ False) → False) ∧ ((p0 → False) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    exact assump_5
  cases assump_3
  case intro assump_14 assump_15 =>
    have assump_50 : (((False → False) ∨ (False → True)) ∨ ((False ∧ p6) → (p6 ∨ p3))) := by
      apply Or.inl
      apply Or.inl
      intro assump_25
      apply False.elim assump_25
    let assump_24 := assump_1 assump_50
    apply False.elim assump_24
  apply And.intro
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    apply False.elim assump_33
  intro assump_38
  have assump_51 : (((False → False) ∨ (False → True)) ∨ ((False ∧ p6) → (p6 ∨ p3))) := by
    apply Or.inl
    apply Or.inl
    intro assump_44
    apply False.elim assump_44
  let assump_43 := assump_1 assump_51
  apply False.elim assump_43


variable (p1 p3 p5 p2 p7 : Prop)
theorem file13_117222 : (((((p2 → p7) ∧ (p2 ∨ p2)) ∧ ((p5 ∧ p5) → False)) ∧ (((p2 → False) → (p1 ∧ p3)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          have assump_58 : ((p2 → False) → (p1 ∧ p3)) := by
            intro assump_19
            apply And.intro
            have assump_59 : p2 := by
              exact assump_10
            let assump_22 := assump_19 assump_59
            apply False.elim assump_22
            have assump_60 : p2 := by
              exact assump_10
            let assump_28 := assump_19 assump_60
            apply False.elim assump_28
          let assump_18 := assump_3 assump_58
          apply False.elim assump_18
        case inr assump_11 =>
          have assump_61 : ((p2 → False) → (p1 ∧ p3)) := by
            intro assump_42
            apply And.intro
            have assump_62 : p2 := by
              exact assump_11
            let assump_45 := assump_42 assump_62
            apply False.elim assump_45
            have assump_63 : p2 := by
              exact assump_11
            let assump_51 := assump_42 assump_63
            apply False.elim assump_51
          let assump_41 := assump_3 assump_61
          apply False.elim assump_41


variable (p2 p0 p6 : Prop)
theorem file13_118665 : ((((((False → False) → False) → False) ∨ (((False ∧ p0) ∨ (p6 → p2)) → False)) → False) → False) := by
  intro assump_30
  have assump_47 : ((((False → False) → False) → False) ∨ (((False ∧ p0) ∨ (p6 → p2)) → False)) := by
    apply Or.inl
    intro assump_34
    have assump_48 : (False → False) := by
      intro assump_38
      apply False.elim assump_38
    let assump_37 := assump_34 assump_48
    apply False.elim assump_37
  let assump_33 := assump_30 assump_47
  apply False.elim assump_33


variable (p2 p7 p1 p4 p6 p3 : Prop)
theorem file13_119223 : (((((True → False) ∧ (p6 → False)) → False) → (((p1 ∧ p7) ∧ (p7 → p7)) → False)) → ((((p3 ∧ p7) ∧ (p7 → False)) ∧ ((p6 ∧ p4) ∧ (p2 ∨ p6))) → (((p6 → False) ∧ (p1 → p2)) → False))) := by
  intro assump_24
  intro assump_25
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_25
    case intro assump_33 assump_34 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        cases assump_35
        case intro assump_37 assump_38 =>
          cases assump_34
          case intro assump_45 assump_46 =>
            cases assump_45
            case intro assump_47 assump_48 =>
              cases assump_46
              case inl assump_53 =>
                have assump_103 : p7 := by
                  exact assump_38
                let assump_75 := assump_36 assump_103
                apply False.elim assump_75
              case inr assump_54 =>
                have assump_104 : p7 := by
                  exact assump_38
                let assump_99 := assump_36 assump_104
                apply False.elim assump_99


variable (p5 p0 p6 p3 p2 p1 p7 p4 : Prop)
theorem file13_120363 : (((((p2 ∧ p4) ∧ (True ∨ p7)) ∧ ((p3 → False) ∧ (False ∨ p6))) ∨ (((p3 ∧ p6) → (p3 ∨ p7)) ∨ ((p1 → True) ∨ (p6 ∨ p5)))) ∨ ((((p7 ∧ p6) → False) → ((True ∧ p0) ∨ (p4 ∧ True))) → (((p1 → p4) → False) ∧ ((p4 → False) → (p4 → p5))))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    exact assump_2


variable (p2 p5 p6 p1 p4 : Prop)
theorem file13_120804 : ((((((p5 → False) → False) ∧ ((False ∧ p5) → (True → False))) → (((p6 → False) → False) → ((False → False) ∨ (p5 → p1)))) ∧ ((((p2 → False) ∧ (True ∨ p4)) → ((p1 → False) → (p1 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_40 : (((p2 → False) ∧ (True ∨ p4)) → ((p1 → False) → (p1 → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_9
      case intro assump_16 assump_17 =>
        cases assump_17
        case inl assump_20 =>
          have assump_41 : p1 := by
            exact assump_11
          let assump_25 := assump_10 assump_41
          apply False.elim assump_25
        case inr assump_21 =>
          have assump_42 : p1 := by
            exact assump_11
          let assump_33 := assump_10 assump_42
          apply False.elim assump_33
    let assump_8 := assump_3 assump_40
    apply False.elim assump_8


variable (p7 p6 p0 p2 p3 p5 p1 p4 : Prop)
theorem file13_121816 : ((((((p7 ∧ p3) ∨ (p2 ∧ p0)) ∧ ((p0 → p7) → False)) ∨ (((p1 → p5) → False) ∨ ((p4 ∧ p6) ∧ (p3 → False)))) ∧ ((((p6 → False) → (p7 ∧ p5)) → False) ∧ (((True ∨ p0) → (True → False)) ∧ ((p5 ∧ p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                have assump_104 : (True ∨ p0) := by
                  apply Or.inl
                  apply True.intro
                let assump_29 := assump_22 assump_104
                have assump_105 : True := by
                  apply True.intro
                let assump_30 := assump_29 assump_105
                apply False.elim assump_30
        case inr assump_9 =>
          cases assump_9
          case intro assump_34 assump_35 =>
            cases assump_3
            case intro assump_42 assump_43 =>
              cases assump_43
              case intro assump_46 assump_47 =>
                have assump_106 : (True ∨ p0) := by
                  apply Or.inl
                  apply True.intro
                let assump_53 := assump_46 assump_106
                have assump_107 : True := by
                  apply True.intro
                let assump_54 := assump_53 assump_107
                apply False.elim assump_54
    case inr assump_5 =>
      cases assump_5
      case inl assump_58 =>
        cases assump_3
        case intro assump_62 assump_63 =>
          cases assump_63
          case intro assump_66 assump_67 =>
            have assump_108 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_73 := assump_66 assump_108
            have assump_109 : True := by
              apply True.intro
            let assump_74 := assump_73 assump_109
            apply False.elim assump_74
      case inr assump_59 =>
        cases assump_59
        case intro assump_78 assump_79 =>
          cases assump_78
          case intro assump_80 assump_81 =>
            cases assump_3
            case intro assump_88 assump_89 =>
              cases assump_89
              case intro assump_92 assump_93 =>
                have assump_110 : (True ∨ p0) := by
                  apply Or.inl
                  apply True.intro
                let assump_99 := assump_92 assump_110
                have assump_111 : True := by
                  apply True.intro
                let assump_100 := assump_99 assump_111
                apply False.elim assump_100


variable (p0 p7 p5 p4 p2 p6 : Prop)
theorem file13_124677 : (((((p0 ∧ p7) → (p2 ∧ p7)) ∧ ((p5 ∨ True) ∨ (p6 ∨ p7))) ∧ (((p4 → True) → False) ∧ ((False → p7) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            have assump_78 : (False → p7) := by
              intro assump_25
              apply False.elim assump_25
            let assump_24 := assump_19 assump_78
            apply False.elim assump_24
        case inr assump_15 =>
          cases assump_7
          case intro assump_33 assump_34 =>
            have assump_79 : (False → p7) := by
              intro assump_40
              apply False.elim assump_40
            let assump_39 := assump_34 assump_79
            apply False.elim assump_39
      case inr assump_13 =>
        cases assump_13
        case inl assump_46 =>
          cases assump_7
          case intro assump_50 assump_51 =>
            have assump_80 : (False → p7) := by
              intro assump_57
              apply False.elim assump_57
            let assump_56 := assump_51 assump_80
            apply False.elim assump_56
        case inr assump_47 =>
          cases assump_7
          case intro assump_65 assump_66 =>
            have assump_81 : (False → p7) := by
              intro assump_72
              apply False.elim assump_72
            let assump_71 := assump_66 assump_81
            apply False.elim assump_71


variable (p3 p2 p4 p1 p6 p5 p0 p7 : Prop)
theorem file13_126338 : (((((p0 ∨ p2) ∨ (p5 → False)) → ((p7 ∨ p1) ∧ (p5 → p6))) ∧ (((p4 ∧ p1) ∨ (True ∨ p0)) → False)) → ((((p3 ∧ p0) ∨ (p3 ∨ p2)) ∧ ((p7 ∧ p2) ∧ (p3 ∧ p7))) ∧ (((p0 ∧ p7) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_65 : ((p4 ∧ p1) ∨ (True ∨ p0)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_65
    apply False.elim assump_8
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_12 assump_13 =>
    have assump_66 : ((p4 ∧ p1) ∨ (True ∨ p0)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_18 := assump_13 assump_66
    apply False.elim assump_18
  cases assump_1
  case intro assump_22 assump_23 =>
    have assump_67 : ((p4 ∧ p1) ∨ (True ∨ p0)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_28 := assump_23 assump_67
    apply False.elim assump_28
  apply And.intro
  cases assump_1
  case intro assump_32 assump_33 =>
    have assump_68 : ((p4 ∧ p1) ∨ (True ∨ p0)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_38 := assump_33 assump_68
    apply False.elim assump_38
  cases assump_1
  case intro assump_42 assump_43 =>
    have assump_69 : ((p4 ∧ p1) ∨ (True ∨ p0)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_48 := assump_43 assump_69
    apply False.elim assump_48
  intro assump_52
  cases assump_1
  case intro assump_55 assump_56 =>
    have assump_70 : ((p4 ∧ p1) ∨ (True ∨ p0)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_61 := assump_56 assump_70
    apply False.elim assump_61


variable (p2 p7 p3 p0 p5 p6 : Prop)
theorem file13_128143 : (((((p6 → p6) → (p0 → False)) ∧ ((True ∧ p3) ∧ (p0 ∧ p7))) → False) ∨ ((((p0 → False) ∨ (p2 → False)) ∧ ((p0 ∨ p2) ∨ (False → p6))) → (((p7 ∨ p0) → (p5 ∧ p0)) → ((False ∧ p6) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          have assump_31 : (p6 → p6) := by
            intro assump_24
            exact assump_24
          let assump_23 := assump_2 assump_31
          have assump_32 : p0 := by
            exact assump_14
          let assump_27 := assump_23 assump_32
          apply False.elim assump_27


variable (p5 p0 p3 p7 p2 p6 p4 p1 : Prop)
theorem file13_128957 : (((((p6 ∧ p4) ∨ (p0 ∧ p1)) ∧ ((p4 ∧ p0) → (False → False))) → (((p2 ∨ True) ∨ (p6 → False)) ∧ ((p5 → p5) → (False → p5)))) ∧ ((((p1 ∨ p7) → (False → False)) ∨ ((p2 ∨ p6) → False)) ∨ (((p3 → p3) → False) → False))) := by
  apply And.intro
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
    case inr assump_5 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
  intro assump_22
  intro assump_23
  apply False.elim assump_23
  apply Or.inl
  apply Or.inl
  intro assump_26
  intro assump_27
  apply False.elim assump_27


variable (p7 p5 p1 p2 p0 : Prop)
theorem file13_129821 : ((((((p1 ∧ p2) → (p1 → p2)) ∨ ((p5 → True) → (p7 ∧ p7))) ∨ (((False ∨ p0) → (False → p0)) ∧ ((p2 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 ∧ p2) → (p1 → p2)) ∨ ((p5 → True) → (p7 ∧ p7))) ∨ (((False ∨ p0) → (False → p0)) ∧ ((p2 → False) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p4 p1 p0 : Prop)
theorem file13_130388 : ((((((p1 ∧ p7) → False) ∧ ((False ∧ p4) ∧ (True → p0))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p1 ∧ p7) → False) ∧ ((False ∧ p4) ∧ (True → p0))) → False) := by
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


variable (p6 p7 p5 p1 : Prop)
theorem file13_130939 : (((((p7 ∧ p1) → (p7 → True)) ∨ ((p5 → False) → (p1 → p6))) → False) → False) := by
  intro assump_1
  have assump_10 : (((p7 ∧ p1) → (p7 → True)) ∨ ((p5 → False) → (p1 → p6))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p7 p2 p5 p0 p4 : Prop)
theorem file13_131319 : ((((((p5 ∨ p2) → (p4 ∨ p4)) → False) → (((p5 → p4) ∧ (False ∧ True)) → ((p0 ∨ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p5 ∨ p2) → (p4 ∨ p4)) → False) → (((p5 → p4) ∧ (False ∧ True)) → ((p0 ∨ p7) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_6
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
    case inr assump_9 =>
      cases assump_6
      case intro assump_22 assump_23 =>
        cases assump_23
        case intro assump_26 assump_27 =>
          apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p4 p6 p5 p2 p1 p3 p7 : Prop)
theorem file13_132151 : ((((((p3 ∨ p3) → (False ∧ p3)) ∧ ((p1 → p4) → False)) → (((p2 ∧ p6) ∧ (p7 ∧ p4)) → ((p5 ∧ True) ∧ (p2 → p6)))) → False) → False) := by
  intro assump_1
  have assump_60 : ((((p3 ∨ p3) → (False ∧ p3)) ∧ ((p1 → p4) → False)) → (((p2 ∧ p6) ∧ (p7 ∧ p4)) → ((p5 ∧ True) ∧ (p2 → p6)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          cases assump_5
          case intro assump_21 assump_22 =>
            have assump_61 : (p1 → p4) := by
              intro assump_28
              exact assump_16
            let assump_27 := assump_22 assump_61
            apply False.elim assump_27
    apply True.intro
    intro assump_34
    cases assump_6
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        cases assump_38
        case intro assump_45 assump_46 =>
          cases assump_5
          case intro assump_51 assump_52 =>
            exact assump_40
  let assump_4 := assump_1 assump_60
  apply False.elim assump_4


variable (p0 p4 p5 p7 p1 p6 p2 p3 : Prop)
theorem file13_133411 : (((((p6 ∧ p6) ∨ (True ∨ p5)) → ((p1 ∨ p6) ∨ (p4 → False))) ∧ (((True ∨ False) ∧ (False → False)) → False)) → ((((p2 → p1) ∧ (p7 → False)) ∨ ((True ∧ p4) ∨ (p1 → False))) → (((p7 ∨ p2) ∨ (p7 ∨ False)) → ((p0 → p2) → (p3 ∧ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_3
  case inl assump_7 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_2
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_1
          case intro assump_21 assump_22 =>
            have assump_379 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_28
              apply False.elim assump_28
            let assump_27 := assump_22 assump_379
            apply False.elim assump_27
      case inr assump_14 =>
        cases assump_14
        case inl assump_34 =>
          cases assump_34
          case intro assump_36 assump_37 =>
            cases assump_1
            case intro assump_42 assump_43 =>
              have assump_380 : ((True ∨ False) ∧ (False → False)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_49
                apply False.elim assump_49
              let assump_48 := assump_43 assump_380
              apply False.elim assump_48
        case inr assump_35 =>
          cases assump_1
          case intro assump_57 assump_58 =>
            have assump_381 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_64
              apply False.elim assump_64
            let assump_63 := assump_58 assump_381
            apply False.elim assump_63
    case inr assump_10 =>
      cases assump_2
      case inl assump_72 =>
        cases assump_72
        case intro assump_74 assump_75 =>
          cases assump_1
          case intro assump_80 assump_81 =>
            have assump_382 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_87
              apply False.elim assump_87
            let assump_86 := assump_81 assump_382
            apply False.elim assump_86
      case inr assump_73 =>
        cases assump_73
        case inl assump_93 =>
          cases assump_93
          case intro assump_95 assump_96 =>
            cases assump_1
            case intro assump_101 assump_102 =>
              have assump_383 : ((True ∨ False) ∧ (False → False)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_108
                apply False.elim assump_108
              let assump_107 := assump_102 assump_383
              apply False.elim assump_107
        case inr assump_94 =>
          cases assump_1
          case intro assump_116 assump_117 =>
            have assump_384 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_123
              apply False.elim assump_123
            let assump_122 := assump_117 assump_384
            apply False.elim assump_122
  case inr assump_8 =>
    cases assump_8
    case inl assump_129 =>
      cases assump_2
      case inl assump_133 =>
        cases assump_133
        case intro assump_135 assump_136 =>
          cases assump_1
          case intro assump_141 assump_142 =>
            have assump_385 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_148
              apply False.elim assump_148
            let assump_147 := assump_142 assump_385
            apply False.elim assump_147
      case inr assump_134 =>
        cases assump_134
        case inl assump_154 =>
          cases assump_154
          case intro assump_156 assump_157 =>
            cases assump_1
            case intro assump_162 assump_163 =>
              have assump_386 : ((True ∨ False) ∧ (False → False)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_169
                apply False.elim assump_169
              let assump_168 := assump_163 assump_386
              apply False.elim assump_168
        case inr assump_155 =>
          cases assump_1
          case intro assump_177 assump_178 =>
            have assump_387 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_184
              apply False.elim assump_184
            let assump_183 := assump_178 assump_387
            apply False.elim assump_183
    case inr assump_130 =>
      apply False.elim assump_130
  cases assump_3
  case inl assump_194 =>
    cases assump_194
    case inl assump_196 =>
      cases assump_2
      case inl assump_200 =>
        cases assump_200
        case intro assump_202 assump_203 =>
          cases assump_1
          case intro assump_208 assump_209 =>
            have assump_388 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_215
              apply False.elim assump_215
            let assump_214 := assump_209 assump_388
            apply False.elim assump_214
      case inr assump_201 =>
        cases assump_201
        case inl assump_221 =>
          cases assump_221
          case intro assump_223 assump_224 =>
            cases assump_1
            case intro assump_229 assump_230 =>
              have assump_389 : ((True ∨ False) ∧ (False → False)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_236
                apply False.elim assump_236
              let assump_235 := assump_230 assump_389
              apply False.elim assump_235
        case inr assump_222 =>
          cases assump_1
          case intro assump_244 assump_245 =>
            have assump_390 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_251
              apply False.elim assump_251
            let assump_250 := assump_245 assump_390
            apply False.elim assump_250
    case inr assump_197 =>
      cases assump_2
      case inl assump_259 =>
        cases assump_259
        case intro assump_261 assump_262 =>
          cases assump_1
          case intro assump_267 assump_268 =>
            have assump_391 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_274
              apply False.elim assump_274
            let assump_273 := assump_268 assump_391
            apply False.elim assump_273
      case inr assump_260 =>
        cases assump_260
        case inl assump_280 =>
          cases assump_280
          case intro assump_282 assump_283 =>
            cases assump_1
            case intro assump_288 assump_289 =>
              have assump_392 : ((True ∨ False) ∧ (False → False)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_295
                apply False.elim assump_295
              let assump_294 := assump_289 assump_392
              apply False.elim assump_294
        case inr assump_281 =>
          cases assump_1
          case intro assump_303 assump_304 =>
            have assump_393 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_310
              apply False.elim assump_310
            let assump_309 := assump_304 assump_393
            apply False.elim assump_309
  case inr assump_195 =>
    cases assump_195
    case inl assump_316 =>
      cases assump_2
      case inl assump_320 =>
        cases assump_320
        case intro assump_322 assump_323 =>
          cases assump_1
          case intro assump_328 assump_329 =>
            have assump_394 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_335
              apply False.elim assump_335
            let assump_334 := assump_329 assump_394
            apply False.elim assump_334
      case inr assump_321 =>
        cases assump_321
        case inl assump_341 =>
          cases assump_341
          case intro assump_343 assump_344 =>
            cases assump_1
            case intro assump_349 assump_350 =>
              have assump_395 : ((True ∨ False) ∧ (False → False)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_356
                apply False.elim assump_356
              let assump_355 := assump_350 assump_395
              apply False.elim assump_355
        case inr assump_342 =>
          cases assump_1
          case intro assump_364 assump_365 =>
            have assump_396 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_371
              apply False.elim assump_371
            let assump_370 := assump_365 assump_396
            apply False.elim assump_370
    case inr assump_317 =>
      apply False.elim assump_317


variable (p7 p0 p2 p6 p4 p3 p5 : Prop)
theorem file13_143314 : (((((p4 → p3) → (True → p2)) ∧ ((p7 → False) ∨ (p5 ∧ p3))) → False) → ((((p7 ∧ p3) ∨ (p0 ∨ p5)) ∧ ((p5 ∧ p4) ∧ (p2 → False))) → (((p3 → p3) ∧ (p3 ∧ False)) → ((p6 ∧ p4) → (p3 ∧ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
  apply True.intro


variable (p3 p1 p7 p6 p5 p4 p0 : Prop)
theorem file13_143880 : (((((p5 → False) → False) → ((p4 → True) ∨ (False → p3))) → False) → ((((p0 → False) ∨ (p1 ∧ p6)) → False) ∧ (((p1 → p7) → False) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_46 : (((p5 → False) → False) → ((p4 → True) ∨ (False → p3))) := by
      intro assump_10
      apply Or.inl
      intro assump_13
      apply True.intro
    let assump_9 := assump_1 assump_46
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case intro assump_17 assump_18 =>
      have assump_47 : (((p5 → False) → False) → ((p4 → True) ∨ (False → p3))) := by
        intro assump_26
        apply Or.inl
        intro assump_29
        apply True.intro
      let assump_25 := assump_1 assump_47
      apply False.elim assump_25
  intro assump_33
  have assump_48 : (((p5 → False) → False) → ((p4 → True) ∨ (False → p3))) := by
    intro assump_39
    apply Or.inl
    intro assump_42
    apply True.intro
  let assump_38 := assump_1 assump_48
  apply False.elim assump_38


variable (p0 p4 p3 p7 p2 : Prop)
theorem file13_144992 : ((((((p0 ∧ p4) → False) ∧ ((True ∧ True) ∧ (p2 → False))) ∧ (((p3 ∧ p3) ∧ (False → True)) → ((p0 ∨ p7) → (p7 ∧ False)))) ∧ ((((True ∨ p3) ∧ (p2 ∧ p3)) ∨ ((p4 ∨ p7) → (False → p2))) ∧ (((p2 ∧ p4) ∧ (p4 → p7)) ∨ ((p0 ∨ True) → (p3 ∧ False))))) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_22 assump_23 =>
              cases assump_22
              case inl assump_24 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case inl assump_28 =>
                    cases assump_27
                    case intro assump_32 assump_33 =>
                      cases assump_23
                      case inl assump_38 =>
                        cases assump_38
                        case intro assump_40 assump_41 =>
                          cases assump_40
                          case intro assump_42 assump_43 =>
                            have assump_146 : p2 := by
                              exact assump_42
                            let assump_59 := assump_11 assump_146
                            apply False.elim assump_59
                      case inr assump_39 =>
                        have assump_147 : (p0 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_65 := assump_39 assump_147
                        let assump_66 := And.right assump_65
                        apply False.elim assump_66
                  case inr assump_29 =>
                    cases assump_27
                    case intro assump_73 assump_74 =>
                      cases assump_23
                      case inl assump_79 =>
                        cases assump_79
                        case intro assump_81 assump_82 =>
                          cases assump_81
                          case intro assump_83 assump_84 =>
                            have assump_148 : p2 := by
                              exact assump_83
                            let assump_101 := assump_11 assump_148
                            apply False.elim assump_101
                      case inr assump_80 =>
                        have assump_149 : (p0 ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_107 := assump_80 assump_149
                        let assump_108 := And.right assump_107
                        apply False.elim assump_108
              case inr assump_25 =>
                cases assump_23
                case inl assump_115 =>
                  cases assump_115
                  case intro assump_117 assump_118 =>
                    cases assump_117
                    case intro assump_119 assump_120 =>
                      have assump_150 : p2 := by
                        exact assump_119
                      let assump_134 := assump_11 assump_150
                      apply False.elim assump_134
                case inr assump_116 =>
                  have assump_151 : (p0 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_140 := assump_116 assump_151
                  let assump_141 := And.right assump_140
                  apply False.elim assump_141


variable (p7 p3 p5 p0 : Prop)
theorem file13_148683 : (((((p3 ∧ p0) ∨ (True ∨ False)) ∨ ((p7 ∧ True) ∨ (p5 ∨ p7))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p3 ∧ p0) ∨ (True ∨ False)) ∨ ((p7 ∧ True) ∨ (p5 ∨ p7))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p3 p6 p4 : Prop)
theorem file13_149058 : (((((True ∧ p1) → False) ∧ ((p6 ∧ p1) ∨ (p3 ∧ p1))) → False) ∧ ((((p4 ∧ True) ∧ (True → False)) → False) ∨ (((True ∨ p1) ∨ (True → False)) → False))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_47 : (True ∧ p1) := by
          apply And.intro
          apply True.intro
          exact assump_9
        let assump_16 := assump_2 assump_47
        apply False.elim assump_16
    case inr assump_7 =>
      cases assump_7
      case intro assump_20 assump_21 =>
        have assump_48 : (True ∧ p1) := by
          apply And.intro
          apply True.intro
          exact assump_21
        let assump_28 := assump_2 assump_48
        apply False.elim assump_28
  apply Or.inl
  intro assump_32
  cases assump_32
  case intro assump_33 assump_34 =>
    cases assump_33
    case intro assump_35 assump_36 =>
      have assump_49 : True := by
        apply True.intro
      let assump_43 := assump_34 assump_49
      apply False.elim assump_43


variable (p1 p3 : Prop)
theorem file13_150218 : (((((p3 → False) → False) → ((p1 ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((p3 → False) → False) → ((p1 ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p4 p6 p2 p0 p5 : Prop)
theorem file13_150633 : ((((((p4 ∨ p5) → (p2 → p4)) ∨ ((p0 ∨ p6) ∧ (p6 → False))) → (((p4 ∨ p0) ∧ (p2 ∧ False)) → False)) → False) → False) := by
  intro assump_5
  have assump_34 : ((((p4 ∨ p5) → (p2 → p4)) ∨ ((p0 ∨ p6) ∧ (p6 → False))) → (((p4 ∨ p0) ∧ (p2 ∧ False)) → False)) := by
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
  let assump_8 := assump_5 assump_34
  apply False.elim assump_8


variable (p1 p2 p0 p6 p4 p7 p3 : Prop)
theorem file13_151402 : (((((p3 ∧ p7) → False) ∧ ((p4 → p0) → (p3 → False))) ∧ (((p1 ∧ p2) → (p3 ∨ True)) → False)) → ((((p0 → p1) → False) ∨ ((p3 ∧ p6) → (True → True))) ∨ (((p3 → p3) → False) ∧ ((p3 ∧ p0) → (p3 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      have assump_27 : ((p1 ∧ p2) → (p3 ∨ True)) := by
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          apply Or.inr
          apply True.intro
      let assump_16 := assump_3 assump_27
      apply False.elim assump_16


variable (p6 p0 p3 p7 p2 : Prop)
theorem file13_152120 : (((((False ∨ False) ∧ (p2 → p3)) ∧ ((p7 ∧ p0) → (True → p6))) ∧ (((p2 → False) ∧ (p2 → p7)) ∧ ((False ∨ p0) → False))) ∨ ((((True → False) → (p2 ∨ p6)) → False) → False)) := by
  apply Or.inr
  intro assump_1
  have assump_15 : ((True → False) → (p2 ∨ p6)) := by
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p7 p1 p0 : Prop)
theorem file13_152645 : ((((((p0 ∨ p1) → False) → False) ∧ (((p3 → True) ∨ (True → False)) → False)) ∨ ((((False ∧ p7) ∨ (False ∧ False)) ∨ ((True → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_28 : ((p3 → True) ∨ (True → False)) := by
        apply Or.inl
        intro assump_11
        apply True.intro
      let assump_10 := assump_5 assump_28
      apply False.elim assump_10
  case inr assump_3 =>
    have assump_29 : (((False ∧ p7) ∨ (False ∧ False)) ∨ ((True → False) → False)) := by
      apply Or.inr
      intro assump_18
      have assump_30 : True := by
        apply True.intro
      let assump_21 := assump_18 assump_30
      apply False.elim assump_21
    let assump_17 := assump_3 assump_29
    apply False.elim assump_17


variable (p7 p4 p2 p6 p3 p5 : Prop)
theorem file13_153548 : (((((p3 ∧ True) → (p6 → False)) ∨ ((p2 ∧ p4) → False)) → False) → ((((p4 ∨ p6) ∧ (p5 ∨ p5)) ∧ ((True → p3) → False)) → (((True ∨ p2) ∨ (p3 ∧ p7)) → ((p5 ∧ True) ∨ (p2 ∨ p3))))) := by
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
          case inl assump_14 =>
            cases assump_13
            case inl assump_18 =>
              apply Or.inl
              apply And.intro
              exact assump_18
              apply True.intro
            case inr assump_19 =>
              apply Or.inl
              apply And.intro
              exact assump_19
              apply True.intro
          case inr assump_15 =>
            cases assump_13
            case inl assump_34 =>
              apply Or.inl
              apply And.intro
              exact assump_34
              apply True.intro
            case inr assump_35 =>
              apply Or.inl
              apply And.intro
              exact assump_35
              apply True.intro
    case inr assump_7 =>
      cases assump_2
      case intro assump_50 assump_51 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          cases assump_52
          case inl assump_54 =>
            cases assump_53
            case inl assump_58 =>
              apply Or.inl
              apply And.intro
              exact assump_58
              apply True.intro
            case inr assump_59 =>
              apply Or.inl
              apply And.intro
              exact assump_59
              apply True.intro
          case inr assump_55 =>
            cases assump_53
            case inl assump_74 =>
              apply Or.inl
              apply And.intro
              exact assump_74
              apply True.intro
            case inr assump_75 =>
              apply Or.inl
              apply And.intro
              exact assump_75
              apply True.intro
  case inr assump_5 =>
    cases assump_5
    case intro assump_88 assump_89 =>
      cases assump_2
      case intro assump_94 assump_95 =>
        cases assump_94
        case intro assump_96 assump_97 =>
          cases assump_96
          case inl assump_98 =>
            cases assump_97
            case inl assump_102 =>
              apply Or.inl
              apply And.intro
              exact assump_102
              apply True.intro
            case inr assump_103 =>
              apply Or.inl
              apply And.intro
              exact assump_103
              apply True.intro
          case inr assump_99 =>
            cases assump_97
            case inl assump_118 =>
              apply Or.inl
              apply And.intro
              exact assump_118
              apply True.intro
            case inr assump_119 =>
              apply Or.inl
              apply And.intro
              exact assump_119
              apply True.intro


variable (p2 p3 p0 p6 p7 : Prop)
theorem file13_156679 : (((((p2 ∧ False) → False) → ((p7 → False) ∧ (False ∨ p3))) ∧ (((p0 ∨ p6) → (p0 ∨ p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p0 ∨ p6) → (p0 ∨ p6)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        exact assump_10
      case inr assump_11 =>
        apply Or.inr
        exact assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


