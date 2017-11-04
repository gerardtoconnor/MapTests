//module SampleData = 

let numberStrings = [|
    ("79639419","7393384");
    ("71415745","8189810");
    ("62488122","6160019");
    ("30950840","6097447");
    ("76631988","5036557");
    ("96994620","6170740");
    ("95191077","5943288");
    ("61165587","1536613");
    ("59069191","1746850");
    ("23061330","6227030");
    ("31060418","6572609");
    ("13130831","1696256");
    ("49027949","1826272");
    ("69860340","7066608");
    ("41092563","6234624");
    ("26537579","9492949");
    ("41613837","9644597");
    ("53541372","1738846");
    ("61869798","9486023");
    ("68336355","1912273");
    ("62398943","8890227");
    ("14080629","2896153");
    ("10940007","4767808");
    ("70382623","6344153");
    ("68269862","4461780");
    ("10882864","5261807");
    ("20499755","6630198");
    ("11201797","1629518");
    ("97254894","7321880");
    ("48636191","4141422");
    ("26030425","1580304");
    ("89149634","2147190");
    ("46681119","9243050");
    ("14600869","7593443");
    ("55626843","7112925");
    ("38024415","8061599");
    ("63837568","4929838");
    ("44545920","9142821");
    ("37032866","4037201");
    ("31470383","8818240");
    ("74571308","3018153");
    ("33321715","3760197");
    ("20029155","4613502");
    ("30078617","2081285");
    ("54779031","9590876");
    ("66584160","5242240");
    ("16051856","8783718");
    ("72670691","6014093");
    ("10936036","3225448");
    ("44971416","3699277");
    ("22758810","7461841");
    ("12569905","3298645");
    ("95981074","4309279");
    ("65827426","7560607");
    ("22794395","6156209");
    ("89403377","8820089");
    ("64005323","1370398");
    ("95954007","9837287");
    ("23651427","6152054");
    ("43130309","1500409");
    ("90303374","9754735");
    ("18284769","2722758");
    ("72552343","7659659");
    ("89366933","6927979");
    ("54759611","7912341");
    ("12980270","1998874");
    ("93877164","4109198");
    ("50557569","5451590");
    ("33988025","5571347");
    ("95008122","5837702");
    ("81024532","1284050");
    ("79449932","9278440");
    ("35128512","6057301");
    ("98306028","4228843");
    ("40973556","9417362");
    ("91790614","3066938");
    ("78385421","8532690");
    ("83943343","9767209");
    ("88878807","1318039");
    ("89191264","1752917");
    ("64050661","4923945");
    ("53437050","3605624");
    ("28149089","9665703");
    ("66343769","3672428");
    ("97330333","9719373");
    ("70993630","5369723");
    ("51624088","1095623");
    ("89464289","4918267");
    ("93344512","2650939");
    ("77949897","3860113");
    ("86688960","7071488");
    ("69120244","3326750");
    ("73071188","2088557");
    ("71052835","4731927");
    ("35921737","5563228");
    ("84859057","3752301");
    ("90970698","3462272");
    ("74810123","3092631");
    ("49087174","4281175");
    ("13584261","9459847");
    ("69985721","9921458");
    ("15795592","6073011");
    ("60274006","4383209");
    ("97511788","4733140");
    ("80760577","6838965");
    ("29615346","2139434");
    ("94439295","4536558");
    ("46574729","8094986");
    ("52042428","1361407");
    ("28525852","2627630");
    ("80153820","4520598");
    ("52325659","3958279");
    ("47954345","2527032");
    ("43456642","3121555");
    ("85462108","5593733");
    ("71506065","8885492");
    ("96856721","8390552");
    ("77615363","6051770");
    ("21217955","3008316");
    ("66964183","2260462");
    ("55745133","8347256");
    ("40517688","6034048");
    ("56082080","4965057");
    ("10393058","6045297");
    ("43362322","7648355");
    ("45867846","8376273");
    ("70588015","5545119");
    ("68562502","5754972");
    ("48470942","1939065");
    ("96556702","3514175");
    ("87248035","2835512");
    ("35810572","4096614");
    ("54040225","2018500");
    ("34074655","3549958");
    ("60348238","5056639");
    ("74329409","2768252");
    ("43811777","6509276");
    ("73078399","1585309");
    ("72925256","1227006");
    ("83240702","1643653");
    ("33106091","2284381");
    ("34582760","8917206");
    ("96014754","9682057");
    ("99532429","3863888");
    ("66505501","6600684");
    ("54652810","5027174");
    ("24066455","4377402");
    ("35434818","1898350");
    ("57892401","7640602");
    ("53280922","9330881");
    ("95934941","8402689");
    ("19737201","9349196");
    ("58145117","3401911");
    ("81196754","2273755");
    ("47556416","4541384");
    ("34654255","4153527");
    ("15696579","8804923");
    ("88148878","2774522");
    ("50501438","1836821");
    ("41817141","3260638");
    ("30423126","9740065");
    ("87711786","9198713");
    ("28348874","7348836");
    ("83302816","1653498");
    ("29872532","2209608");
    ("18089881","1724161");
    ("70793667","6226254");
    ("22021549","2944450");
    ("93604005","7598017");
    ("14939213","7737380");
    ("46410336","9196691");
    ("65109688","6446303");
    ("12421006","8303887");
    ("51402009","7768843");
    ("39331109","1783637");
    ("10549090","7175578");
    ("84793649","8712854");
    ("56333706","7830440");
    ("24717600","5254646");
    ("89503073","8839988");
    ("11374120","6864279");
    ("93367536","9565169");
    ("57488625","3571640");
    ("14871961","5138326");
    ("96525561","7921595");
    ("92249806","6811281");
    ("41905419","9553953");
    ("91640255","2989066");
    ("71588708","1936562");
    ("60617725","6481696");
    ("18440644","6572695");
    ("79373725","6909442");
    ("19442705","2589243");
    ("93173765","4341324");
    ("72018514","3673122");
    ("90776031","4118472");
    ("63105282","3276608");
    ("49196903","2970231");
    ("34626612","8011081");
    ("83957303","8359207");
    ("28492637","9520618");
    ("68558170","1479735");
    ("39331032","1658258");
    ("87735518","6377889");
    ("24456619","4137074");
    ("11629228","3527385");
    ("22262681","6792920");
    ("59168521","7734462");
    ("40076202","8248144");
    ("44319323","1840820");
    ("23620008","6085071");
    ("56129743","5848303");
    ("67433547","3072006");
    ("40739859","4796826");
    ("16794780","2283448");
    ("43598709","9054328");
    ("95612943","5494052");
    ("77589344","9288999");
    ("87914687","7370400");
    ("85644944","1420366");
    ("63528830","2937054");
    ("15796776","8469078");
    ("71789521","6810948");
    ("12777906","2026142");
    ("65419552","2003000");
    ("20556789","5659988");
    ("82893010","6334921");
    ("98278110","8272337");
    ("89164018","8009928");
    ("89118369","1159840");
    ("72085274","8367534");
    ("17168133","6023755");
    ("85009280","2430845");
    ("42975234","4020830");
    ("87597201","6126902");
    ("39423673","1571908");
    ("70099899","5059083");
    ("11254916","1861850");
    ("45515526","7138282");
    ("43412354","6874868");
    ("94345315","4551604");
    ("78713301","2632526");
    ("21170578","7279711");
    ("38910342","9336293");
    ("92106054","6603395");
    ("50359169","3648171");
    ("34103202","9755041");
    ("59747925","1064150");
    ("29416592","7964616");
    ("83516911","4921762");
    ("31791900","5868329");
    ("67291038","6054322");
    ("22549856","5722142");
    ("13392518","1964984");
    ("61429081","2245114");
    ("14733289","7216804");
    ("17695240","2193764");
    ("44787630","5218622");
    ("34641166","1056161");
    ("55696895","8176203");
    ("69960640","5679427");
    ("96623693","8472325");
    ("35920222","8891845");
    ("76058260","4646824");
    ("84864737","8295104");
    ("37180244","4980386");
    ("75548188","1541143");
    ("35545125","9130268");
    ("95269019","4271496");
    ("38696730","3345880");
    ("25280341","1398740");
    ("38413163","3244334");
    ("24232052","4722750");
    ("52376034","6192401");
    ("88592371","6394004");
    ("85895319","5120894");
    ("42576619","7696375");
    ("27402917","3040839");
    ("68873788","6521583");
    ("21466079","6993944");
    ("34634609","8374118");
    ("10164165","2963961");
    ("16592661","7907098");
    ("87771418","8240658");
    ("92487332","3070357");
    ("46976034","7108234");
    ("55040558","3722246");
    ("24007893","2256471");
    ("71394187","3449818");
    ("31212510","8356119");
    ("24295368","9441755");
    ("63568596","6831498");
    ("17061256","5011352");
    ("36064257","7924827");
    ("74580684","7114269");
    ("92505476","3956843");
    ("28367509","6424094");
    ("92999357","4060335");
    ("34852413","6767522");
    ("16175288","9543707");
    ("47677458","9889500");
    ("34451108","1014442");
    ("54324156","3718711");
    ("46467475","4474617");
    ("48906293","5535876");
    ("68415505","6606997");
    ("50994886","6600998");
    ("17910511","9208382");
    ("32050787","4580489");
    ("65618897","9074157");
    ("95632871","8695927");
    ("41388205","1361052");
    ("89952629","1723484");
    ("88091023","7225560");
    ("35383906","6340391");
    ("42465584","7894987");
    ("59957326","1084243");
    ("48168066","4594964");
    ("46525936","6622444");
    ("73992028","1889025");
    ("43478463","1087413");
    ("27326621","4546483");
    ("27622216","3964001");
    ("77247862","1325245");
    ("16528871","6547455");
    ("73114436","4431342");
    ("53122775","7029400");
    ("88347807","7849027");
    ("87668514","7248346");
    ("58802487","8616841");
    ("92502596","7974590");
    ("26567412","8498188");
    ("36604719","4273452");
    ("97588289","9266487");
    ("29935297","9705546");
    ("32724755","3303279");
    ("72709689","8141078");
    ("64220975","3923356");
    ("47993786","3244475");
    ("15020369","7574724");
    ("62200444","6605886");
    ("17229214","5304401");
    ("65528809","7235482");
    ("65404049","3907655");
    ("20278778","6674632");
    ("82777547","7280584");
    ("40418635","1414235");
    ("57573273","9735899");
    ("42011885","1622542");
    ("33067057","9899797");
    ("78979162","6115393");
    ("90225663","2329719");
    ("69774904","4473818");
    ("35080636","1094103");
    ("66459659","1850438");
    ("22820410","3233737");
    ("71562181","5350251");
    ("83604635","2322517");
    ("53240535","6092683");
    ("14350588","3768575");
    ("54863455","4640075");
    ("95320445","5786718");
    ("89033438","9726899");
    ("99187667","6898728");
    ("28090095","8318680");
    ("62860957","4817409");
    ("45901401","9240178");
    ("49978552","1282986");
    ("48341507","2970976");
    ("93981018","8938156");
    ("76641391","8205552");
    ("82079632","8243937");
    ("29818021","5092805");
    ("88971405","8879471");
    ("65936667","5748820");
    ("53572852","3267912");
    ("58391284","9934558");
    ("92128053","7206916");
    ("59681255","1974446");
    ("66011719","7126871");
    ("81790165","5279724");
    ("99833572","3896020");
    ("28179055","7545219");
    ("49545833","8056100");
    ("32446590","7303186");
    ("50799884","2551179");
    ("38467031","7518391");
    ("54324631","8297695");
    ("26574979","2190176");
    ("23328963","1460479");
    ("23891489","6312884");
    ("95689152","8158320");
    ("41038200","3214543");
    ("69710064","7513001");
    ("53149198","5010556");
    ("94881953","3595009");
    ("80869088","9320423");
    ("11474773","6084677");
    ("69875321","1859639");
    ("13189894","1174419");
    ("85093120","9097800");
    ("36071720","3507364");
    ("53784047","4059188");
    ("77866702","2721381");
    ("78575788","7838840");
    ("87353268","5083982");
    ("78461233","7461496");
    ("58956094","8138225");
    ("26465710","9310808");
    ("90773964","3720808");
    ("24431955","4557935");
    ("79129890","8018400");
    ("91802094","5514166");
    ("72756391","4843673");
    ("99320237","6021292");
    ("87906054","9092780");
    ("38571428","3151698");
    ("66118783","8538958");
    ("72189239","3520530");
    ("24443527","7017435");
    ("50823395","7081296");
    ("71241616","9054253");
    ("29360075","8554415");
    ("38732316","7737762");
    ("10948912","8315119");
    ("47638496","6493249");
    ("68758331","8735763");
    ("10820240","3705716");
    ("64321164","2662978");
    ("51092283","3962407");
    ("77094520","7547242");
    ("48760770","2653567");
    ("69261146","2903563");
    ("42686640","4885003");
    ("29405250","9752592");
    ("22064549","1636400");
    ("51159721","7647783");
    ("80311981","5582023");
    ("69801839","2210528");
    ("94731742","2968770");
    ("70885206","7098284");
    ("12920498","1500372");
    ("77038760","7381320");
    ("99553152","8867334");
    ("44032685","7306697");
    ("33634819","1591145");
    ("26034666","3484398");
    ("44557587","4224510");
    ("34588479","1377476");
    ("77414309","7235272");
    ("94594461","6388950");
    ("28137223","4176457");
    ("34614480","7901660");
    ("17570470","9491719");
    ("26413428","1149882");
    ("26868756","8223511");
    ("42973315","5769126");
    ("44736100","8107452");
    ("30848813","4533391");
    ("39396122","9648430");
    ("96411398","2065581");
    ("68822716","4044139");
    ("45933056","6882501");
    ("43647719","5262215");
    ("19243523","8316180");
    ("96903058","4087430");
    ("64727200","4808039");
    ("11740438","3794022");
    ("13865271","5890934");
    ("24797733","4383446");
    ("93669834","3207624");
    ("64818006","2091266");
    ("16959935","4102462");
    ("60447268","4066951");
    ("51897967","5517235");
    ("10702169","6651057");
    ("98150102","6134799");
    ("44333582","4241337");
    ("50438078","4527616");
    ("32255413","1888624");
    ("88092442","5997914");
    ("28281722","9132236");
    ("30139965","6859894");
    ("18139171","8894106");
    ("12837326","1546881");
    ("40155917","6558505");
    ("46710160","6699165");
    ("54361462","4216346");
    ("50863691","5571896");
    ("35356674","8761784");
    ("43533913","5695090");
    ("93696847","7502196");
    ("23629035","2209804");
    ("50107704","5049515");
    ("93939634","8342428");
    ("71573092","1596552");
    ("75897235","3025132");
    ("88222108","5420434");
    ("72713356","5943985");
    ("73699891","6990459");
    ("97128520","5477460");
    ("42602404","8597419");
    ("37755536","8529668");
    ("47805394","2136384");
    ("47468257","7093712");
    ("96989758","5085526");
    ("24942838","2659918");
    ("24136178","1397337");
    ("19197879","1940703");
    ("98596245","1803722");
    ("75531416","3587458");
    ("84692165","4932485");
    ("60803957","2837731");
    ("40828999","5759743");
    ("73982574","3303899");
    ("35416819","6418564");
    ("74603543","8648070");
    ("74888953","8436905");
    ("93673552","6263887");
    ("56086000","3568823");
    ("75504173","2952538");
    ("34579533","6154600");
    ("66705708","7051393");
    ("80133700","9938695");
    ("28326828","5733810");
    ("86864549","6713188");
    ("83774413","4010064");
    ("53006398","4333445");
    ("27458964","3866657");
    ("16324884","7206590");
    ("76798478","4495700");
    ("76093902","2186228");
    ("59017919","2325086");
    ("37954322","2502318");
    ("65437378","1842675");
    ("89442148","1074663");
    ("82780403","8221113");
    ("85744000","5854618");
    ("30014272","3719023");
    ("23885092","7912439");
    ("16886061","3345951");
    ("54963327","4650773");
    ("92743345","4038979");
    ("69817312","1352099");
    ("39186186","8183204");
    ("74714358","2348087");
    ("28099839","7744574");
    ("91985696","3116780");
    ("14797090","8394169");
    ("86797404","4770956");
    ("99141290","4864514");
    ("62782578","5172858");
    ("16446545","7949913");
    ("50087520","9311247");
    ("36905439","1256703");
    ("12520343","8992672");
    ("63804778","7665174");
    ("30510158","6705466");
    ("56339874","5667567");
    ("68470700","1877738");
    ("74798828","3609512");
    ("87905771","5103586");
    ("33336347","4682306");
    ("23188637","9788557");
    ("44989106","7039844");
    ("86902558","5409838");
    ("18666738","7454285");
    ("97873236","3581444");
    ("87926585","4533253");
    ("95223194","3925986");
    ("73042560","5864989");
    ("38780692","8377728");
    ("87018021","2068439");
    ("48880317","6645450");
    ("47414047","3487769");
    ("62743517","4595784");
    ("63969898","1328300");
    ("86126512","5017420");
    ("89433803","1061084");
    ("42222897","6596734");
    ("36380244","7290714");
    ("14431546","5126730");
    ("36387926","5288818");
    ("82697440","2052275");
    ("91303810","7420253");
    ("66769337","5232905");
    ("78534528","5750375");
    ("43627988","2977094");
    ("67322207","9254539");
    ("59891185","9606943");
    ("25439779","2379638");
    ("88206861","4504671");
    ("42592118","7688920");
    ("76092035","7927619");
    ("96865683","7785196");
    ("40607162","2726802");
    ("28638584","2361560");
    ("69010526","6024422");
    ("74594206","7033360");
    ("15192535","4570242");
    ("20509727","5908650");
    ("53605512","3309846");
    ("78187752","3679075");
    ("16840517","7383347");
    ("88464299","7139796");
    ("38653652","3840412");
    ("84469281","6759698");
    ("97508232","4095049");
    ("87313536","1383657");
    ("51513628","9617687");
    ("84277394","1505037");
    ("41478646","7894538");
    ("30303225","5809797");
    ("51599185","2214472");
    ("80733546","1349172");
    ("18048790","3174330");
    ("15278111","8684156");
    ("21404510","6501684");
    ("78276114","5737698");
    ("65791564","3046748");
    ("26724344","6382263");
    ("71351987","1106987");
    ("35502125","6733110");
    ("24231331","2379107");
    ("43297144","5097373");
    ("27048802","4746113");
    ("78702428","3864612");
    ("83353972","9498184");
    ("35009249","3099563");
    ("19696235","8315607");
    ("36394840","3292837");
    ("19022656","9788453");
    ("88728900","9125611");
    ("44571477","3616052");
    ("16555013","6954184");
    ("11557086","1138530");
    ("59708949","3108980");
    ("59284003","9241124");
    ("30233809","7980555");
    ("39021915","9344613");
    ("31099358","1015694");
    ("89075566","2212429");
    ("57210012","1217707");
    ("33196893","2992618");
    ("85518144","3574197");
    ("67081959","2134802");
    ("38537218","6592651");
    ("44781853","7843212");
    ("78468205","3318433");
    ("77640543","9504898");
    ("43252386","4085179");
    ("67501138","5421856");
    ("67225564","3664791");
    ("49237117","5563888");
    ("66102061","6823424");
    ("15136366","8510897");
    ("30685001","9802477");
    ("14412967","6377945");
    ("84174148","5327851");
    ("60574178","2058846");
    ("95310731","1373756");
    ("78332722","5886181");
    ("57692229","9147563");
    ("14837410","8028648");
    ("14589972","2323161");
    ("18281578","1538586");
    ("47312090","1722480");
    ("69746024","5718250");
    ("22302766","8483983");
    ("87633549","4972316");
    ("66145662","7915821");
    ("32273728","1389611");
    ("62230512","8369235");
    ("27813520","6021987");
    ("58342129","8738910");
    ("32553905","9881388");
    ("57008700","6621707");
    ("46211780","8535413");
    ("64210653","7037151");
    ("40829702","4020559");
    ("90991221","5646155");
    ("98827627","7764699");
    ("16165359","3674446");
    ("14506247","1455399");
    ("99431966","5715136");
    ("15052364","2428757");
    ("11047373","6694911");
    ("71928785","3366536");
    ("92735490","8975093");
    ("68908055","8343167");
    ("22700006","1722491");
    ("49499965","6051779");
    ("27059234","3731333");
    ("78801125","7733328");
    ("27857779","8954769");
    ("76413559","2135809");
    ("46100239","7999804");
    ("28094605","9827106");
    ("63327397","7432499");
    ("10782913","3999024");
    ("96815756","3088603");
    ("55591707","6239331");
    ("28864878","1873700");
    ("17247321","3736523");
    ("14463515","6415335");
    ("71158917","8700908");
    ("32343551","2941324");
    ("28136179","2623288");
    ("42013237","1764004");
    ("11235673","8789468");
    ("98650947","3997340");
    ("78069315","6420923");
    ("74912211","5757074");
    ("33238241","2012477");
    ("10187693","3902482");
    ("89210622","9908008");
    ("33445649","3611097");
    ("20755337","5659968");
    ("50585421","4475770");
    ("21353571","4507004");
    ("55156195","1428515");
    ("58749900","9441319");
    ("25675001","8890572");
    ("87110058","2447328");
    ("11479275","7102162");
    ("44651310","6590206");
    ("26706345","2135258");
    ("18144768","9268889");
    ("64569029","4640259");
    ("41045150","7960648");
    ("63649696","8793758");
    ("74049269","2834131");
    ("11039688","1878368");
    ("65315492","1834099");
    ("76333605","5843626");
    ("99098739","7187482");
    ("95251658","4309200");
    ("56893144","4977319");
    ("40941555","3188536");
    ("12323259","9664838");
    ("51533598","4475154");
    ("16050935","8650183");
    ("13279219","5791087");
    ("88374370","2619491");
    ("23329920","7911539");
    ("69561822","2100467");
    ("97603528","5198948");
    ("51694780","7341458");
    ("74905759","2514246");
    ("20520535","8748848");
    ("96966090","8114877");
    ("12707122","6516415");
    ("74103626","2671632");
    ("25745145","3720459");
    ("91712524","9697527");
    ("62730214","6554322");
    ("70669335","4499776");
    ("43312159","5399805");
    ("14517649","2513464");
    ("21486340","8977328");
    ("96970482","8145343");
    ("57196527","8735741");
    ("75241417","7819618");
    ("83843449","6550734");
    ("54181276","2862180");
    ("74973796","4015514");
    ("70520255","4412062");
    ("44922567","6127917");
    ("48216694","1100460");
    ("96693974","3002087");
    ("70187438","7073120");
    ("41077492","7264701");
    ("66874138","6987281");
    ("13423426","1059996");
    ("87206142","7505832");
    ("33539078","3632868");
    ("63698188","5090352");
    ("43025029","1010677");
    ("98509336","5725677");
    ("99145206","3341171");
    ("19423663","2338832");
    ("45826095","2612848");
    ("92948472","8171589");
    ("56657586","8889136");
    ("24882615","5713956");
    ("94907535","7048350");
    ("93938807","8241227");
    ("97006493","4506019");
    ("47984887","1084145");
    ("93790439","2758022");
    ("71269295","5072660");
    ("18019235","2436025");
    ("70744201","2994429");
    ("99801374","9410132");
    ("28965583","8971417");
    ("64345920","6028526");
    ("21266562","4251514");
    ("78949780","3677897");
    ("49775147","8192653");
    ("37114707","5880219");
    ("77006380","6751644");
    ("10350863","7384016");
    ("36348098","4022075");
    ("98016994","9447320");
    ("96498316","5820612");
    ("19182313","8897793");
    ("58851776","2716963");
    ("69548324","8077394");
    ("85483257","3932530");
    ("63469249","5893071");
    ("15121407","9181487");
    ("88710809","5658622");
    ("75380122","7250899");
    ("89836185","4060328");
    ("28524110","3878138");
    ("62139786","1865426");
    ("15549913","7037420");
    ("71929319","1886986");
    ("34880239","6174632");
    ("63723575","5049969");
    ("44151325","5537527");
    ("14278902","7686328");
    ("29956062","1434459");
    ("88517827","9829053");
    ("42178344","9469077");
    ("59758075","9256666");
    ("97830321","4237469");
    ("44168836","6266471");
    ("90500725","1227934");
    ("93820247","8768195");
    ("52374894","3551048");
    ("19794097","6497737");
    ("88301149","4452049");
    ("66171146","8692809");
    ("78085375","1694118");
    ("82475244","5294842");
    ("42722600","3727187");
    ("62891750","5536646");
    ("34274804","8567119");
    ("17431444","4449324");
    ("53650661","1497906");
    ("28316156","6476584");
    ("47526355","4548132");
    ("10176513","9211569");
    ("16938215","8825605");
    ("86303341","4998927");
    ("61879587","7996059");
    ("82175812","6942126");
    ("33722860","5513944");
    ("17832656","2579949");
    ("25244888","9515364");
    ("26310641","7379717");
    ("65330832","9297654");
    ("80569616","3294841");
    ("92373926","3664034");
    ("92267686","5941483");
    ("14843586","9563431");
    ("76123779","4379296");
    ("56433269","8860561");
    ("57794954","1856331");
    ("69058859","2292401");
    ("93536841","8352695");
    ("50479078","3990569");
    ("89981035","9128968");
    ("89255788","5311945");
    ("71290116","8406711");
    ("20326198","6608918");
    ("49440109","9788821");
    ("59214562","4592497");
    ("52652387","1787157");
    ("13325955","7723822");
    ("76838469","6866005");
    ("51587231","7553333");
    ("92236823","4554934");
    ("81977922","6275639");
    ("78629500","2210387");
    ("12921676","1881945");
    ("64198095","3847886");
    ("38554414","6120774");
    ("99498466","1986315");
    ("46307864","5557896");
    ("11441688","3220348");
    ("56595061","9027821");
    ("50436909","9905537");
    ("64634209","9746798");
    ("68442308","7665961");
    ("41633372","7368561");
    ("50120332","6265641");
    ("10330138","8549761");
    ("88377792","2455810");
    ("48148429","7474268");
    ("43027843","3513445");
    ("14239128","7858160");
    ("39693290","7623137");
    ("96053770","2291198");
    ("62479323","5200445");
    ("80237021","3482379");
    ("61416910","3746755");
    ("45731234","6763215");
    ("85682848","8310032");
    ("56585730","1181250");
    ("41061447","1075185");
    ("68082832","2112168");
    ("98549420","1618963");
    ("19647046","7706915");
    ("11483832","5661415");
    ("87554559","5777799");
    ("18509907","7957218");
    ("12144466","1249415");
    ("67999546","7958151");
    ("93078454","7699243");
    ("34195610","2576648");
    ("97511033","7083661");
    ("78763144","4355039");
    ("52525951","9470110");
    ("88593817","5864039");
    ("34354520","5060740");
    ("61654093","9885724");
    ("66722321","2223436");
    ("35482612","2396605");
    ("85264705","6903282");
    ("36875478","4737507");
    ("33552805","1683816");
    ("70867909","2909542");
    ("14087908","7402720");
    ("41080455","1290652");
    ("32231969","4813247");
    ("66323461","4585848");
    ("40444997","7706272");
    ("90592054","8258059");
    ("30767683","3407826");
    ("86567394","3172230");
    ("21378720","8689857");
    ("42037865","6947730");
    ("22622260","6369322");
    ("47115784","5830903");
    ("80903682","4609533");
    ("48854619","7555554");
    ("25141577","5386596");
    ("25333450","1368075");
    ("38269090","2489331");
    ("99987315","1701325");
    ("95713096","4253801");
    ("45110715","7738284");
    ("50601631","2045231");
    ("87108355","4488511");
    ("89685343","3587485");
    ("60409852","4517064");
    ("47268018","6259009");
    ("20665532","4385806");
    ("75785037","6543886");
    ("46825447","5195115");
    ("69526375","1390083");
    ("62189283","6218457");
    ("91186958","3853807");
    ("58353990","6179819");
    ("81953376","9591185");
    ("89503048","3016334");
    ("36891911","9842632");
    ("62940004","5275336");
    ("84634167","6241488");
    ("30916132","7534683");
    ("16929323","9840400");
    ("41711731","2254506");
    ("86474308","6680578");
    ("97768761","3347615");
    ("50105780","6911503");
    ("92270666","7480411");
    ("68034576","5136307");
    ("91228058","9603045");
    ("95907177","3741461");
    ("13417689","9353393");
    ("92361760","2097866");
    ("70207170","7883233");
    ("99038106","6933930");
    ("59680043","1857483");
    ("96725130","9482677");
    ("14040214","3947692");
    ("86044643","4909575");
    ("25733976","6991290");
    ("51625325","9797126");
    ("21752876","3003219");
    ("14216980","3691302");
    ("63099249","7643419");
    ("48870649","2447835");
    ("72398250","5126597");
    ("89327540","3182447");
    ("44240324","2478329");
    ("34242215","6062390");
    ("81811729","6864934");
    ("23134135","8527058");
    ("10682510","2998433");
    ("37390626","6188119");
    ("37916842","1705374");
    ("40385227","8890098");
    ("95855268","9074933");
    ("46173856","6833986");
    ("28384151","3806423");
    ("50964706","4679182");
    ("33395350","3713041");
    ("15584077","4808875");
    ("91356271","4651243");
    ("16142173","2728802");
    ("97280045","2798852");
    ("61295463","4501594");
    ("93509655","4784944");
    ("90792665","3498777");
    ("68633215","2814851");
    ("26859058","1621403");
    ("80600578","4361779");
    ("12260868","3288414");
|]    

let sample2 = [|  
    ("17664391","4789625");
    ("68712773","7951153");
    ("63477795","6391772");
    ("16305035","3694371");
    ("30667474","8365107");
    ("91366478","8626555");
    ("80684099","4812562");
    ("33467842","8762705");
    ("21032857","7002764");
    ("73048283","8001247");
    ("88618478","5751134");
    ("78351615","1547477");
    ("78103207","6349616");
    ("84196003","2712273");
    ("18164492","4938341");
    ("31049538","7565229");
    ("33186141","7745642");
    ("73196254","9793992");
    ("68987732","6222936");
    ("87889748","2304717");
    ("62413781","7677772");
    ("82297369","4694753");
    ("52463866","8406898");
    ("66678154","3549239");
    ("76356863","6148358");
    ("50086426","3293470");
    ("20543183","9762766");
    ("80195998","5780962");
    ("97723519","5253013");
    ("71409531","1404288");
|]
