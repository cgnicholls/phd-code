us := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
specificquartics := [
    1/405*(-23797686*z + 56814607)*l1^4 + 1/405*(48474800*z - 119835852)*l1^3*l2 + 1/405*(-43143584*z + 73352414)*l1^3*l3 + 1/225*(-31372*z + 83855)*l1^3*l4 + 1/405*(-15010996*z + 
        54657369)*l1^2*l2^2 + 1/135*(-1049444*z - 2331237)*l1^2*l2*l3 + 1/225*(61732*z - 181780)*l1^2*l2*l4 + 1/405*(12598388*z - 38267054)*l1^2*l3^2 + 1/225*(-22264*z - 
        168840)*l1^2*l3*l4 + 1/405*(1986556*z - 13076801)*l1*l2^3 + 1/405*(-2451064*z + 33007576)*l1*l2^2*l3 + 1/225*(-22264*z + 163210)*l1*l2^2*l4 + 1/135*(-1777072*z - 
        6296814)*l1*l2*l3^2 + 1/75*(-4048*z - 9380)*l1*l2*l3*l4 + 1/405*(4027760*z + 12542988)*l1*l3^3 + 1/225*(12144*z - 64160)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/45*(6072*z - 
        10130)*l2^4 + 1/45*(-24288*z + 40520)*l2^3*l3 + 1/225*(-2024*z - 28140)*l2^3*l4 + 1/9*(6072*z - 9680)*l2^2*l3^2 + 1/225*(12144*z + 76540)*l2^2*l3*l4 + l2^2*l4^2 + 
        1/45*(-4048*z + 36020)*l2*l3^3 + 1/75*(-8096*z - 19510)*l2*l3^2*l4 + 1/45*(-16192*z - 39395)*l3^4 + 1/225*(16192*z + 40520)*l3^3*l4,
    1/2560*(-482459004*z + 1157800069)*l1^4 + 1/5120*(1967519727*z - 4895811163)*l1^3*l2 + 1/5120*(-1740188853*z + 2921589511)*l1^3*l3 + 1/800*(-198369*z + 536085)*l1^3*l4 + 
        1/10240*(-1230239745*z + 4550015957)*l1^2*l2^2 + 1/5120*(-124518141*z - 317572649)*l1^2*l2*l3 + 1/800*(390339*z - 1164185)*l1^2*l2*l4 + 1/5120*(516098547*z - 
        1593701641)*l1^2*l3^2 + 1/400*(-70389*z - 552090)*l1^2*l3*l4 + 1/2560*(40243311*z - 272164087)*l1*l2^3 + 1/2560*(-45464895*z + 675235057)*l1*l2^2*l3 + 1/400*(-70389*z + 
        528085)*l1*l2^2*l4 + 1/2560*(-113665437*z - 373645609)*l1*l2*l3^2 + 1/400*(-38394*z - 92015)*l1*l2*l3*l4 + 1/1280*(40550463*z + 124313843)*l1*l3^3 + 1/400*(38394*z - 
        212035)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/80*(19197*z - 32005)*l2^4 + 1/20*(-19197*z + 32005)*l2^3*l3 + 1/400*(-6399*z - 92015)*l2^3*l4 + 1/16*(19197*z - 31205)*l2^2*l3^2 + 
        1/200*(19197*z + 124020)*l2^2*l3*l4 + l2^2*l4^2 + 1/40*(-6399*z + 60010)*l2*l3^3 + 1/200*(-38394*z - 94015)*l2*l3^2*l4 + 1/20*(-12798*z - 31505)*l3^4 + 1/100*(12798*z + 
        32005)*l3^3*l4,
    1/3125*(-1447559694*z + 3482453327)*l1^4 + 1/3125*(2953029744*z - 7370924812)*l1^3*l2 + 1/3125*(-2604395808*z + 4346614174)*l1^3*l3 + 1/625*(-242172*z + 657855)*l1^3*l4 + 
        1/3125*(-927198468*z + 3454252249)*l1^2*l2^2 + 1/3125*(-184667868*z - 500219471)*l1^2*l2*l3 + 1/625*(476532*z - 1429780)*l1^2*l2*l4 + 1/3125*(777833028*z - 
        2420279854)*l1^2*l3^2 + 1/625*(-171864*z - 1368840)*l1^2*l3*l4 + 1/3125*(120703212*z - 826529441)*l1*l2^3 + 1/3125*(-130663512*z + 2034692696)*l1*l2^2*l3 + 1/625*(-171864*z 
        + 1303210)*l1*l2^2*l4 + 1/3125*(-348633936*z - 1108258442)*l1*l2*l3^2 + 1/625*(-93744*z - 228140)*l1*l2*l3*l4 + 1/3125*(242578224*z + 738031628)*l1*l3^3 + 1/625*(93744*z - 
        528160)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/125*(46872*z - 78130)*l2^4 + 1/125*(-187488*z + 312520)*l2^3*l3 + 1/625*(-15624*z - 228140)*l2^3*l4 + 1/25*(46872*z - 76880)*l2^2*l3^2 
        + 1/625*(93744*z + 612540)*l2^2*l3*l4 + l2^2*l4^2 + 1/125*(-31248*z + 300020)*l2*l3^3 + 1/625*(-187488*z - 462530)*l2*l3^2*l4 + 1/125*(-124992*z - 309395)*l3^4 + 
        1/625*(124992*z + 312520)*l3^3*l4,
    1/12960*(-12493896774*z + 30098196119)*l1^4 + 1/25920*(50988023447*z - 127486626963)*l1^3*l2 + 1/25920*(-44899408973*z + 74691660311)*l1^3*l3 + 1/1800*(-1004369*z + 
        2736085)*l1^3*l4 + 1/51840*(-32092343465*z + 120033683757)*l1^2*l2^2 + 1/8640*(-1055980607*z - 2952951483)*l1^2*l2*l3 + 1/1800*(1976339*z - 5949185)*l1^2*l2*l4 + 
        1/25920*(13460261747*z - 42055752641)*l1^2*l3^2 + 1/900*(-356389*z - 2862090)*l1^2*l3*l4 + 1/12960*(1041595451*z - 7180677187)*l1*l2^3 + 1/12960*(-1101080015*z + 
        17603106857)*l1*l2^2*l3 + 1/900*(-356389*z + 2718085)*l1*l2^2*l4 + 1/4320*(-1014769079*z - 3168526203)*l1*l2*l3^2 + 1/300*(-64798*z - 159005)*l1*l2*l3*l4 + 
        1/6480*(1045094543*z + 3166258143)*l1*l3^3 + 1/900*(194394*z - 1107035)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/180*(97197*z - 162005)*l2^4 + 1/45*(-97197*z + 162005)*l2^3*l3 + 
        1/900*(-32399*z - 477015)*l2^3*l4 + 1/36*(97197*z - 160205)*l2^2*l3^2 + 1/450*(97197*z + 639020)*l2^2*l3*l4 + l2^2*l4^2 + 1/90*(-32399*z + 315010)*l2*l3^3 + 1/150*(-64798*z 
        - 160505)*l2*l3^2*l4 + 1/45*(-64798*z - 160880)*l3^4 + 1/225*(64798*z + 162005)*l3^3*l4,
    1/12005*(-21487856706*z + 51808005407)*l1^4 + 1/12005*(43852934160*z - 109760482252)*l1^3*l2 + 1/12005*(-38580786144*z + 64054074814)*l1^3*l3 + 1/1225*(-930372*z + 
        2538855)*l1^3*l4 + 1/12005*(-13819715676*z + 51813122569)*l1^2*l2^2 + 1/12005*(-2714015172*z - 7734470111)*l1^2*l2*l3 + 1/1225*(1830732*z - 5521780)*l1^2*l2*l4 + 
        1/12005*(11592104988*z - 36309007054)*l1^2*l3^2 + 1/1225*(-660264*z - 5328840)*l1^2*l3*l4 + 1/12005*(1791206196*z - 12398640401)*l1*l2^3 + 1/12005*(-1866206184*z + 
        30318652376)*l1*l2^2*l3 + 1/1225*(-660264*z + 5053210)*l1*l2^2*l4 + 1/12005*(-5272148016*z - 16286494442)*l1*l2*l3^2 + 1/1225*(-360144*z - 888140)*l1*l2*l3*l4 + 
        1/12005*(3591235920*z + 10852160588)*l1*l3^3 + 1/1225*(360144*z - 2064160)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/245*(180072*z - 300130)*l2^4 + 1/245*(-720288*z + 1200520)*l2^3*l3 +
        1/1225*(-60024*z - 888140)*l2^3*l4 + 1/49*(180072*z - 297680)*l2^2*l3^2 + 1/1225*(360144*z + 2376540)*l2^2*l3*l4 + l2^2*l4^2 + 1/245*(-120048*z + 1176020)*l2*l3^3 + 
        1/1225*(-720288*z - 1788530)*l2*l3^2*l4 + 1/245*(-480192*z - 1194395)*l3^4 + 1/1225*(480192*z + 1200520)*l3^3*l4,
    1/40960*(-125249132052*z + 302144185789)*l1^4 + 1/81920*(511272575055*z - 1280542015483)*l1^3*l2 + 1/81920*(-449537651541*z + 745391932231)*l1^3*l3 + 1/3200*(-3174369*z + 
        8672085)*l1^3*l4 + 1/163840*(-322528895073*z + 1211111884277)*l1^2*l2^2 + 1/81920*(-31562136573*z - 91048108169)*l1^2*l2*l3 + 1/3200*(6246339*z - 18864185)*l1^2*l2*l4 + 
        1/81920*(135266314227*z - 424367868841)*l1^2*l3^2 + 1/1600*(-1126389*z - 9120090)*l1^2*l3*l4 + 1/40960*(10439885247*z - 72454749127)*l1*l2^3 + 1/40960*(-10774115583*z + 
        176888408977)*l1*l2^2*l3 + 1/1600*(-1126389*z + 8640085)*l1*l2^2*l4 + 1/40960*(-30867461757*z - 94697680009)*l1*l2*l3^2 + 1/1600*(-614394*z - 1520015)*l1*l2*l3*l4 + 
        1/20480*(10459545855*z + 31553946563)*l1*l3^3 + 1/1600*(614394*z - 3536035)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/320*(307197*z - 512005)*l2^4 + 1/80*(-307197*z + 512005)*l2^3*l3 + 
        1/1600*(-102399*z - 1520015)*l2^3*l4 + 1/64*(307197*z - 508805)*l2^2*l3^2 + 1/800*(307197*z + 2032020)*l2^2*l3*l4 + l2^2*l4^2 + 1/160*(-102399*z + 1008010)*l2*l3^3 + 
        1/800*(-614394*z - 1528015)*l2*l3^2*l4 + 1/80*(-204798*z - 510005)*l3^4 + 1/400*(204798*z + 512005)*l3^3*l4,
    1/32805*(-160837300722*z + 388140095647)*l1^4 + 1/32805*(328294364048*z - 822634512972)*l1^3*l2 + 1/32805*(-288535930592*z + 478008751934)*l1^3*l3 + 1/2025*(-2542372*z + 
        6950855)*l1^3*l4 + 1/32805*(-103612730620*z + 389485969929)*l1^2*l2^2 + 1/10935*(-6743764748*z - 19615978677)*l1^2*l2*l3 + 1/2025*(5002732*z - 15121780)*l1^2*l2*l4 + 
        1/32805*(86907214268*z - 272953698254)*l1^2*l3^2 + 1/2025*(-1804264*z - 14640840)*l1^2*l3*l4 + 1/32805*(13405599508*z - 93205232081)*l1*l2^3 + 1/32805*(-13744391080*z + 
        227296077016)*l1*l2^2*l3 + 1/2025*(-1804264*z + 13861210)*l1*l2^2*l4 + 1/10935*(-13252811152*z - 40466526414)*l1*l2*l3^2 + 1/675*(-328048*z - 813380)*l1*l2*l3*l4 + 
        1/32805*(26851056848*z + 80909269068)*l1*l3^3 + 1/2025*(984144*z - 5680160)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/405*(492072*z - 820130)*l2^4 + 1/405*(-1968288*z + 3280520)*l2^3*l3
        + 1/2025*(-164024*z - 2440140)*l2^3*l4 + 1/81*(492072*z - 816080)*l2^2*l3^2 + 1/2025*(984144*z + 6520540)*l2^2*l3*l4 + l2^2*l4^2 + 1/405*(-328048*z + 3240020)*l2*l3^3 + 
        1/675*(-656096*z - 1633510)*l2*l3^2*l4 + 1/405*(-1312192*z - 3270395)*l3^4 + 1/2025*(1312192*z + 3280520)*l3^3*l4,
    1/100000*(-747787508838*z + 1805079220279)*l1^4 + 1/200000*(3052850038551*z - 7652333359123)*l1^3*l2 + 1/200000*(-2682350020557*z + 4440964514071)*l1^3*l3 + 1/5000*(-7749969*z +
        21200085)*l1^3*l4 + 1/400000*(-1927850038569*z + 7252426259117)*l1^2*l2^2 + 1/200000*(-187899998397*z - 549795449009)*l1^2*l2*l3 + 1/5000*(15249939*z - 46125185)*l1^2*l2*l4 
        + 1/200000*(808500015987*z - 2541304415041)*l1^2*l3^2 + 1/2500*(-2749989*z - 22350090)*l1^2*l3*l4 + 1/100000*(62325000699*z - 433886485507)*l1*l2^3 + 
        1/100000*(-63599995599*z + 1057266479017)*l1*l2^2*l3 + 1/2500*(-2749989*z + 21150085)*l1*l2^2*l4 + 1/100000*(-185250008997*z - 563745505009)*l1*l2*l3^2 + 1/2500*(-1499994*z 
        - 3725015)*l1*l2*l3*l4 + 1/50000*(62400000399*z + 187871001503)*l1*l3^3 + 1/2500*(1499994*z - 8675035)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/500*(749997*z - 1250005)*l2^4 + 
        1/125*(-749997*z + 1250005)*l2^3*l3 + 1/2500*(-249999*z - 3725015)*l2^3*l4 + 1/100*(749997*z - 1245005)*l2^2*l3^2 + 1/1250*(749997*z + 4975020)*l2^2*l3*l4 + l2^2*l4^2 + 
        1/250*(-249999*z + 2475010)*l2*l3^3 + 1/1250*(-1499994*z - 3737515)*l2*l3^2*l4 + 1/125*(-499998*z - 1246880)*l3^4 + 1/625*(499998*z + 1250005)*l3^3*l4,
    1/73205*(-801886019742*z + 1936051610447)*l1^4 + 1/73205*(1636911303408*z - 4104128383372)*l1^3*l2 + 1/73205*(-1437942853152*z + 2379580962334)*l1^3*l3 + 1/3025*(-5673372*z + 
        15525855)*l1^3*l4 + 1/73205*(-517013475300*z + 1946064343129)*l1^2*l2^2 + 1/73205*(-100657881084*z - 295811964431)*l1^2*l2*l3 + 1/3025*(11163732*z - 33781780)*l1^2*l2*l4 + 
        1/73205*(433644920868*z - 1363845086254)*l1^2*l3^2 + 1/3025*(-4026264*z - 32760840)*l1^2*l3*l4 + 1/73205*(66832139148*z - 465707507681)*l1*l2^3 + 1/73205*(-67961506200*z + 
        1134143273816)*l1*l2^2*l3 + 1/3025*(-4026264*z + 30991210)*l1*l2^2*l4 + 1/73205*(-198968450256*z - 603988287242)*l1*l2*l3^2 + 1/3025*(-2196144*z - 5460140)*l1*l2*l3*l4 + 
        1/73205*(133797145008*z + 402581382668)*l1*l3^3 + 1/3025*(2196144*z - 12720160)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/605*(1098072*z - 1830130)*l2^4 + 1/605*(-4392288*z + 
        7320520)*l2^3*l3 + 1/3025*(-366024*z - 5460140)*l2^3*l4 + 1/121*(1098072*z - 1824080)*l2^2*l3^2 + 1/3025*(2196144*z + 14580540)*l2^2*l3*l4 + l2^2*l4^2 + 1/605*(-732048*z + 
        7260020)*l2*l3^3 + 1/3025*(-4392288*z - 10950530)*l2*l3^2*l4 + 1/605*(-2928192*z - 7305395)*l3^4 + 1/3025*(2928192*z + 7320520)*l3^3*l4,
    1/207360*(-3218256243132*z + 7771244673989)*l1^4 + 1/414720*(13139374749935*z - 32949759886683)*l1^3*l2 + 1/414720*(-11540380292021*z + 19090815111431)*l1^3*l3 + 
        1/7200*(-16070369*z + 43992085)*l1^3*l4 + 1/829440*(-8302080669953*z + 31262871627477)*l1^2*l2^2 + 1/138240*(-269136690431*z - 793556673123)*l1^2*l2*l3 + 1/7200*(31622339*z 
        - 95724185)*l1^2*l2*l4 + 1/414720*(3481657367027*z - 10954941688841)*l1^2*l3^2 + 1/3600*(-5702389*z - 46440090)*l1^2*l3*l4 + 1/207360*(268216013807*z - 
        1870369553527)*l1*l2^3 + 1/207360*(-272023136063*z + 4552913288177)*l1*l2^2*l3 + 1/3600*(-5702389*z + 43920085)*l1*l2^2*l4 + 1/69120*(-266499076319*z - 
        807456732003)*l1*l2*l3^2 + 1/1200*(-1036798*z - 2580005)*l1*l2*l3*l4 + 1/103680*(268439962175*z + 807327131763)*l1*l3^3 + 1/3600*(3110394*z - 18036035)*l1*l3^2*l4 - 
        4*l1*l3*l4^2 + 1/720*(1555197*z - 2592005)*l2^4 + 1/180*(-1555197*z + 2592005)*l2^3*l3 + 1/3600*(-518399*z - 7740015)*l2^3*l4 + 1/144*(1555197*z - 2584805)*l2^2*l3^2 + 
        1/1800*(1555197*z + 10332020)*l2^2*l3*l4 + l2^2*l4^2 + 1/360*(-518399*z + 5148010)*l2*l3^3 + 1/600*(-1036798*z - 2586005)*l2*l3^2*l4 + 1/180*(-1036798*z - 2587505)*l3^4 + 
        1/900*(1036798*z + 2592005)*l3^3*l4,
    1/142805*(-3053650553766*z + 7374633857807)*l1^4 + 1/142805*(6233793672240*z - 15634848101452)*l1^3*l2 + 1/142805*(-5474476273824*z + 9053710802014)*l1^3*l3 + 
        1/4225*(-11067372*z + 30303855)*l1^3*l4 + 1/142805*(-1969775509716*z + 7419999678169)*l1^2*l2^2 + 1/142805*(-382856455692*z - 1131768339311)*l1^2*l2*l3 + 1/4225*(21777732*z 
        - 65941780)*l1^2*l2*l4 + 1/142805*(1652126224788*z - 5200171387054)*l1^2*l3^2 + 1/4225*(-7854264*z - 64008840)*l1^2*l3*l4 + 1/142805*(254493505116*z - 1775678771201)*l1*l2^3
        + 1/142805*(-257570591544*z + 4320922626776)*l1*l2^2*l3 + 1/4225*(-7854264*z + 60523210)*l1*l2^2*l4 + 1/142805*(-759317398416*z - 2297252986442)*l1*l2*l3^2 + 
        1/4225*(-4284144*z - 10668140)*l1*l2*l3*l4 + 1/142805*(509349020400*z + 1531293733388)*l1*l3^3 + 1/4225*(4284144*z - 24864160)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/845*(2142072*z -
        3570130)*l2^4 + 1/845*(-8568288*z + 14280520)*l2^3*l3 + 1/4225*(-714024*z - 10668140)*l2^3*l4 + 1/169*(2142072*z - 3561680)*l2^2*l3^2 + 1/4225*(4284144*z + 
        28476540)*l2^2*l3*l4 + l2^2*l4^2 + 1/845*(-1428048*z + 14196020)*l2*l3^3 + 1/4225*(-8568288*z - 21378530)*l2*l3^2*l4 + 1/845*(-5712192*z - 14259395)*l3^4 + 1/4225*(5712192*z
        + 14280520)*l3^3*l4,
    1/384160*(-11051758838934*z + 26692740004519)*l1^4 + 1/768320*(45123379893207*z - 113186188033363)*l1^3*l2 + 1/768320*(-39623053809933*z + 65514356386711)*l1^3*l3 + 
        1/9800*(-29772369*z + 81536085)*l1^3*l4 + 1/1536640*(-28520753013225*z + 107464097746157)*l1^2*l2^2 + 1/768320*(-2770116291261*z - 8205486548849)*l1^2*l2*l3 + 
        1/9800*(58584339*z - 177429185)*l1^2*l2*l4 + 1/768320*(11960667967347*z - 37657301120641)*l1^2*l3^2 + 1/4900*(-10564389*z - 86142090)*l1^2*l3*l4 + 1/384160*(921050492571*z -
        6429326701987)*l1*l2^3 + 1/384160*(-930650640975*z + 15640792001257)*l1*l2^2*l3 + 1/4900*(-10564389*z + 81438085)*l1*l2^2*l4 + 1/384160*(-2750163041637*z - 
        8310708082609)*l1*l2*l3^2 + 1/4900*(-5762394*z - 14357015)*l1*l2*l3*l4 + 1/192080*(921615207183*z + 2769912692543)*l1*l3^3 + 1/4900*(5762394*z - 33467035)*l1*l3^2*l4 - 
        4*l1*l3*l4^2 + 1/980*(2881197*z - 4802005)*l2^4 + 1/245*(-2881197*z + 4802005)*l2^3*l3 + 1/4900*(-960399*z - 14357015)*l2^3*l4 + 1/196*(2881197*z - 4792205)*l2^2*l3^2 + 
        1/2450*(2881197*z + 19159020)*l2^2*l3*l4 + l2^2*l4^2 + 1/490*(-960399*z + 9555010)*l2*l3^3 + 1/2450*(-5762394*z - 14381515)*l2*l3^2*l4 + 1/245*(-1920798*z - 4795880)*l3^4 + 
        1/1225*(1920798*z + 4802005)*l3^3*l4,
    1/253125*(-9598238974794*z + 23183879767327)*l1^4 + 1/253125*(19594651486544*z - 49155279916812)*l1^3*l2 + 1/253125*(-17204755968608*z + 28441989746174)*l1^3*l3 + 
        1/5625*(-19617172*z + 53732855)*l1^3*l4 + 1/253125*(-6193260801868*z + 23340748098249)*l1^2*l2^2 + 1/84375*(-400831347356*z - 1189271627157)*l1^2*l2*l3 + 1/5625*(38601532*z 
        - 116929780)*l1^2*l2*l4 + 1/253125*(5194480966028*z - 16358074299854)*l1^2*l3^2 + 1/5625*(-13921864*z - 113568840)*l1^2*l3*l4 + 1/253125*(799906641412*z - 
        5585706827441)*l1*l2^3 + 1/253125*(-807168159112*z + 13585497796696)*l1*l2^2*l3 + 1/5625*(-13921864*z + 107353210)*l1*l2^2*l4 + 1/84375*(-796631839312*z - 
        2405079212814)*l1*l2*l3^2 + 1/1875*(-2531248*z - 6309380)*l1*l2*l3*l4 + 1/253125*(1600667579024*z + 4809671159628)*l1*l3^3 + 1/5625*(7593744*z - 44128160)*l1*l3^2*l4 - 
        4*l1*l3*l4^2 + 1/1125*(3796872*z - 6328130)*l2^4 + 1/1125*(-15187488*z + 25312520)*l2^3*l3 + 1/5625*(-1265624*z - 18928140)*l2^3*l4 + 1/225*(3796872*z - 6316880)*l2^2*l3^2 +
        1/5625*(7593744*z + 50512540)*l2^2*l3*l4 + l2^2*l4^2 + 1/1125*(-2531248*z + 25200020)*l2*l3^3 + 1/1875*(-5062496*z - 12637510)*l2*l3^2*l4 + 1/1125*(-10124992*z - 
        25284395)*l3^4 + 1/5625*(10124992*z + 25312520)*l3^3*l4,
    1/655360*(-32175135152244*z + 77721611392669)*l1^4 + 1/1310720*(131371473404367*z - 329584760880763)*l1^3*l2 + 1/1310720*(-115340843470293*z + 190647661399111)*l1^3*l3 + 
        1/12800*(-50790369*z + 139136085)*l1^3*l4 + 1/2621440*(-83053091324385*z + 313059812349557)*l1^2*l2^2 + 1/1310720*(-8059774562301*z - 23945579594249)*l1^2*l2*l3 + 
        1/12800*(99942339*z - 302784185)*l1^2*l2*l4 + 1/1310720*(34829500456947*z - 109702378073641)*l1^2*l3^2 + 1/6400*(-18022389*z - 147072090)*l1^2*l3*l4 + 
        1/655360*(2681418548991*z - 18729739841287)*l1*l2^3 + 1/655360*(-2702809486335*z + 45546055216657)*l1*l2^2*l3 + 1/6400*(-18022389*z + 139008085)*l1*l2^2*l4 + 
        1/655360*(-8015314967037*z - 24180133081609)*l1*l2*l3^2 + 1/6400*(-9830394*z - 24512015)*l1*l2*l3*l4 + 1/327680*(2682676839423*z + 8059328925443)*l1*l3^3 + 1/6400*(9830394*z
        - 57152035)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/1280*(4915197*z - 8192005)*l2^4 + 1/320*(-4915197*z + 8192005)*l2^3*l3 + 1/6400*(-1638399*z - 24512015)*l2^3*l4 + 1/256*(4915197*z 
        - 8179205)*l2^2*l3^2 + 1/3200*(4915197*z + 32704020)*l2^2*l3*l4 + l2^2*l4^2 + 1/640*(-1638399*z + 16320010)*l2*l3^3 + 1/3200*(-9830394*z - 24544015)*l2*l3^2*l4 + 
        1/320*(-3276798*z - 8184005)*l3^4 + 1/1600*(3276798*z + 8192005)*l3^3*l4,
    1/417605*(-26132388230826*z + 63128110130207)*l1^4 + 1/417605*(53349911050320*z - 133852800240652)*l1^3*l2 + 1/417605*(-46837293201504*z + 77408355369214)*l1^3*l3 + 
        1/7225*(-32364372*z + 88668855)*l1^3*l4 + 1/417605*(-16865296623756*z + 63581180973769)*l1^2*l2^2 + 1/417605*(-3272300056212*z - 9732815368511)*l1^2*l2*l3 + 
        1/7225*(63684732*z - 192961780)*l1^2*l2*l4 + 1/417605*(14145369744588*z - 44560329007054)*l1^2*l3^2 + 1/7225*(-22968264*z - 187488840)*l1^2*l3*l4 + 1/417605*(2177812164036*z
        - 15215768062001)*l1*l2^3 + 1/417605*(-2193199856904*z + 36995419161176)*l1*l2^2*l3 + 1/7225*(-22968264*z + 177193210)*l1*l2^2*l4 + 1/417605*(-6512617848816*z - 
        19634384998442)*l1*l2*l3^2 + 1/7225*(-12528144*z - 31248140)*l1*l2*l3*l4 + 1/417605*(4357434644880*z + 13088563386188)*l1*l3^3 + 1/7225*(12528144*z - 72864160)*l1*l3^2*l4 - 
        4*l1*l3*l4^2 + 1/1445*(6264072*z - 10440130)*l2^4 + 1/1445*(-25056288*z + 41760520)*l2^3*l3 + 1/7225*(-2088024*z - 31248140)*l2^3*l4 + 1/289*(6264072*z - 10425680)*l2^2*l3^2
        + 1/7225*(12528144*z + 83376540)*l2^2*l3*l4 + l2^2*l4^2 + 1/1445*(-4176048*z + 41616020)*l2*l3^3 + 1/7225*(-25056288*z - 62568530)*l2*l3^2*l4 + 1/1445*(-16704192*z - 
        41724395)*l3^4 + 1/7225*(16704192*z + 41760520)*l3^3*l4,
    1/1049760*(-82574452303062*z + 199483995262439)*l1^4 + 1/2099520*(337158074803415*z - 845961414476883)*l1^3*l2 + 1/2099520*(-295986277593101*z + 489129420724631)*l1^3*l3 + 
        1/16200*(-81356369*z + 222912085)*l1^3*l4 + 1/4199040*(-213183518323433*z + 803787232669677)*l1^2*l2^2 + 1/699840*(-6892010321471*z - 20518033286523)*l1^2*l2*l3 + 
        1/16200*(160088339*z - 485109185)*l1^2*l2*l4 + 1/2099520*(89401130835827*z - 281664301843841)*l1^2*l3^2 + 1/8100*(-28868389*z - 235710090)*l1^2*l3*l4 + 
        1/1049760*(6881523223067*z - 48089153883427)*l1*l2^3 + 1/1049760*(-6924888792143*z + 116908690086377)*l1*l2^2*l3 + 1/8100*(-28868389*z + 222750085)*l1*l2^2*l4 + 
        1/349920*(-6861966201719*z - 20676582099003)*l1*l2*l3^2 + 1/2700*(-5248798*z - 13095005)*l1*l2*l3*l4 + 1/524880*(6884074138895*z + 20675138678463)*l1*l3^3 + 
        1/8100*(15746394*z - 91611035)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/1620*(7873197*z - 13122005)*l2^4 + 1/405*(-7873197*z + 13122005)*l2^3*l3 + 1/8100*(-2624399*z - 
        39285015)*l2^3*l4 + 1/324*(7873197*z - 13105805)*l2^2*l3^2 + 1/4050*(7873197*z + 52407020)*l2^2*l3*l4 + l2^2*l4^2 + 1/810*(-2624399*z + 26163010)*l2*l3^3 + 
        1/1350*(-5248798*z - 13108505)*l2*l3^2*l4 + 1/405*(-5248798*z - 13111880)*l3^4 + 1/2025*(5248798*z + 13122005)*l3^3*l4,
    1/651605*(-63636316913862*z + 153738697279247)*l1^4 + 1/651605*(129916906379568*z - 325988532285772)*l1^3*l2 + 1/651605*(-114047742628512*z + 188452451984734)*l1^3*l3 + 
        1/9025*(-50499372*z + 138375855)*l1^3*l4 + 1/651605*(-41075317663380*z + 154886354042329)*l1^2*l2^2 + 1/651605*(-7965749762124*z - 23733324974831)*l1^2*l2*l3 + 
        1/9025*(99369732*z - 301141780)*l1^2*l2*l4 + 1/651605*(34450816560468*z - 108551196974254)*l1^2*l3^2 + 1/9025*(-35838264*z - 292680840)*l1^2*l3*l4 + 
        1/651605*(5303246936988*z - 37066348401281)*l1*l2^3 + 1/651605*(-5333238676920*z + 90101790694616)*l1*l2^2*l3 + 1/9025*(-35838264*z + 276571210)*l1*l2^2*l4 + 
        1/651605*(-15869163751056*z - 47795645415242)*l1*l2*l3^2 + 1/9025*(-19548144*z - 48780140)*l1*l2*l3*l4 + 1/651605*(10610022313968*z + 31861770784268)*l1*l3^3 + 
        1/9025*(19548144*z - 113760160)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/1805*(9774072*z - 16290130)*l2^4 + 1/1805*(-39096288*z + 65160520)*l2^3*l3 + 1/9025*(-3258024*z - 
        48780140)*l2^3*l4 + 1/361*(9774072*z - 16272080)*l2^2*l3^2 + 1/9025*(19548144*z + 130140540)*l2^2*l3*l4 + l2^2*l4^2 + 1/1805*(-6516048*z + 64980020)*l2*l3^3 + 
        1/9025*(-39096288*z - 97650530)*l2*l3^2*l4 + 1/1805*(-26064192*z - 65115395)*l3^4 + 1/9025*(26064192*z + 65160520)*l3^3*l4,
    1/1600000*(-191858400035388*z + 463524267881029)*l1^4 + 1/3200000*(783382400154351*z - 1965745335436123)*l1^3*l2 + 1/3200000*(-687670400082357*z + 1136223432056071)*l1^3*l3 + 
        1/20000*(-123999969*z + 339800085)*l1^3*l4 + 1/6400000*(-495382400154369*z + 1868146823036117)*l1^2*l2^2 + 1/3200000*(-48025599993597*z - 143184727796009)*l1^2*l2*l3 + 
        1/20000*(243999939*z - 739500185)*l1^2*l2*l4 + 1/3200000*(207744000063987*z - 654640871660041)*l1^2*l3^2 + 1/10000*(-43999989*z - 359400090)*l1^2*l3*l4 + 
        1/1600000*(15988800002799*z - 111768183942007)*l1*l2^3 + 1/1600000*(-16070399982399*z + 271664263916017)*l1*l2^2*l3 + 1/10000*(-43999989*z + 339600085)*l1*l2^2*l4 + 
        1/1600000*(-47856000035997*z - 144079928020009)*l1*l2*l3^2 + 1/10000*(-23999994*z - 59900015)*l1*l2*l3*l4 + 1/800000*(15993600001599*z + 48023936006003)*l1*l3^3 + 
        1/10000*(23999994*z - 139700035)*l1*l3^2*l4 - 4*l1*l3*l4^2 + 1/2000*(11999997*z - 20000005)*l2^4 + 1/500*(-11999997*z + 20000005)*l2^3*l3 + 1/10000*(-3999999*z - 
        59900015)*l2^3*l4 + 1/400*(11999997*z - 19980005)*l2^2*l3^2 + 1/5000*(11999997*z + 79900020)*l2^2*l3*l4 + l2^2*l4^2 + 1/1000*(-3999999*z + 39900010)*l2*l3^3 + 
        1/5000*(-23999994*z - 59950015)*l2*l3^2*l4 + 1/500*(-7999998*z - 19987505)*l3^4 + 1/2500*(7999998*z + 20000005)*l3^3*l4
];