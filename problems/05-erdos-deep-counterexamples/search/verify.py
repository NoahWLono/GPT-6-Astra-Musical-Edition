import csv,json,math,itertools
from collections import Counter
from pathlib import Path
p=Path(__file__).parent
rows=list(csv.DictReader((p/'results_6_60.csv').open()))
bylength={}
for row in rows:
    row={k:int(v) for k,v in row.items()}
    n=row['n']; lengths=tuple(row[f'k{i}'] for i in (1,2,3)); gens=tuple(row[f'g{i}'] for i in (1,2,3))
    aps=[[(j*g)%n for j in range(a)] for a,g in zip(lengths,gens)]
    assert all(len(set(ap))==len(ap) for ap in aps)
    assert math.gcd(n,*gens)==1
    assert all(2*(a-1)<=n//math.gcd(n,g) for a,g in zip(lengths,gens))
    multiplicities=Counter(min((x-y)%n,(y-x)%n) for ap in aps for x,y in itertools.combinations(ap,2))
    assert sorted(multiplicities.values())==list(range(1,row['k'])),(row,multiplicities)
    row.update(aps=aps,multiplicities=dict(sorted(multiplicities.items())),orders=[n//math.gcd(n,g) for g in gens])
    bylength.setdefault(lengths,row)
(p/'verified_witnesses.json').write_text(json.dumps(list(bylength.values()),indent=2)+'\n')
print(f'Independently verified {len(rows)} search hits and {len(bylength)} length tuples by explicit unordered-pair enumeration.')
for key,row in bylength.items():
    print(key,'n',row['n'],'g',tuple(row[f'g{i}'] for i in (1,2,3)),'orders',row['orders'],'claimed',row['claimed'])
    if not row['claimed']:
        print('APs',row['aps']);print('multiplicities',row['multiplicities'])
