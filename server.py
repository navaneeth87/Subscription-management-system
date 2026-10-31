#!/usr/bin/env python3
"""Brightloop Subscription Management - backend (Python standard library only).
Run:  python server.py   ->  http://localhost:8000   (serves ../frontend too)
Optional password-reset email: set SMTP_HOST, SMTP_PORT, SMTP_USER, SMTP_PASS, SMTP_FROM."""
import json, os, re, hashlib, secrets, sqlite3, threading, calendar, mimetypes, smtplib, urllib.parse, datetime as dt
from email.message import EmailMessage
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler

BASE = os.path.dirname(os.path.abspath(__file__))
WEB = os.path.realpath(os.path.join(BASE, '..', 'frontend'))
db = sqlite3.connect(os.path.join(BASE, 'brightloop.db'), check_same_thread=False)
db.execute('create table if not exists docs(col text, id text, data text, primary key(col,id))')
LOCK = threading.RLock()

class Err(Exception):
    def __init__(s, code, msg): s.code, s.msg = code, msg

# ---------- storage ----------
def uid(): return secrets.token_hex(4)
def allc(c): return [json.loads(r[0]) for r in db.execute('select data from docs where col=?', (c,))]
def getd(c, i):
    r = db.execute('select data from docs where col=? and id=?', (c, i)).fetchone()
    return json.loads(r[0]) if r else None
def put(c, d): db.execute('insert or replace into docs values(?,?,?)', (c, d['id'], json.dumps(d)))
def nextno(k):
    m = getd('meta', k) or {'id': k, 'n': 0}; m['n'] += 1; put('meta', m); return m['n']

# ---------- dates / validation ----------
def today(): return dt.date.today().isoformat()
def aD(d, n): return (dt.date.fromisoformat(d) + dt.timedelta(days=n)).isoformat()
def aM(d, n):
    x = dt.date.fromisoformat(d); m = x.month - 1 + n; y = x.year + m // 12; m = m % 12 + 1
    return dt.date(y, m, min(x.day, calendar.monthrange(y, m)[1])).isoformat()
def adv(d, p): return {'daily': lambda: aD(d, 1), 'weekly': lambda: aD(d, 7), 'monthly': lambda: aM(d, 1), 'yearly': lambda: aM(d, 12)}[p]()
def isdate(s):
    try: dt.date.fromisoformat(s); return True
    except Exception: return False
def hpw(p, salt=None):
    salt = salt or secrets.token_hex(8)
    return salt + '$' + hashlib.pbkdf2_hmac('sha256', p.encode(), salt.encode(), 100000).hex()
def chk(p, h): return secrets.compare_digest(hpw(p, h.split('$')[0]), h)
def pwerr(p):
    if len(p) <= 8: return 'Password must be more than 8 characters.'
    if not re.search('[A-Z]', p): return 'Password needs an uppercase letter.'
    if not re.search('[a-z]', p): return 'Password needs a lowercase letter.'
    if not re.search('[^A-Za-z0-9]', p): return 'Password needs a special character.'
def num(b, k, lo=0, hi=None, req=True):
    try: v = float(b.get(k))
    except Exception:
        if req: raise Err(400, f'{k} must be a number.')
        return 0
    if v < lo or (hi is not None and v > hi): raise Err(400, f'{k} is out of range.')
    return v
def req(b, k):
    v = str(b.get(k, '')).strip()
    if not v: raise Err(400, f'{k} is required.')
    return v
def pub(u): return {k: u[k] for k in ('id', 'email', 'role', 'name')}

# ---------- money ----------
PER = {'daily': 30, 'weekly': 4.345, 'monthly': 1, 'yearly': 1 / 12}
def tm(): return {t['id']: t['rate'] for t in allc('taxes')}
def totals(lines, discs=(), T=None):
    T = T if T is not None else tm()
    sub = sum(l['qty'] * l['price'] for l in lines)
    tax = sum(l['qty'] * l['price'] * T.get(l.get('tax'), 0) / 100 for l in lines)
    dis = sum(d['amt'] for d in discs); tx = tax * (sub - dis) / sub if sub else 0
    return dict(subtotal=round(sub, 2), discount=round(dis, 2), tax=round(tx, 2), total=round(sub - dis + tx, 2))
def apply_discounts(lines, discs, t):
    out = []
    for d in discs:
        if d['from'] and t < d['from'] or d['to'] and t > d['to'] or d['limit'] and d['used'] >= d['limit']: continue
        el = [l for l in lines if l.get('prod') == d['prod']] if d['scope'] == 'product' else lines
        base = sum(l['qty'] * l['price'] for l in el); q = sum(l['qty'] for l in el)
        if not el or base < d['minPurchase'] or q < d['minQty']: continue
        out.append({'id': d['id'], 'name': d['name'], 'amt': round(min(base, d['value'] if d['kind'] == 'fixed' else base * d['value'] / 100), 2)})
    return out
def paidmap():
    m = {}
    for p in allc('payments'): m[p['inv']] = m.get(p['inv'], 0) + p['amt']
    return m
def dstatus(i, pm):
    bal = i['total'] - pm.get(i['id'], 0)
    return 'Overdue' if i['status'] == 'Confirmed' and i['due'] < today() and bal > 0.005 else i['status']

# ---------- lines / names ----------
def build_lines(raw):
    if not isinstance(raw, list) or not raw: raise Err(400, 'Add at least one product line.')
    out = []
    for l in raw:
        p = getd('products', l.get('prod'))
        if not p: raise Err(400, 'Unknown product.')
        vi = int(l.get('vi', -1))
        if vi >= len(p['variants']) or vi < -1: raise Err(400, 'Unknown variant.')
        q = num(l, 'qty', 0.0001)
        tax = l.get('tax') or ''
        if tax and not getd('taxes', tax): raise Err(400, 'Unknown tax.')
        out.append({'prod': p['id'], 'vi': vi, 'qty': q, 'price': p['price'] + (p['variants'][vi]['extra'] if vi >= 0 else 0), 'tax': tax})
    return out
def named(lines):
    P = {p['id']: p for p in allc('products')}; out = []
    for l in lines:
        p = P.get(l.get('prod')); n = l.get('name') or (p['name'] + (f" ({p['variants'][l['vi']]['val']})" if p and l['vi'] >= 0 else '') if p else '?')
        out.append({**l, 'name': n})
    return out

# ---------- subscription lifecycle ----------
FLOW = ['Draft', 'Quotation', 'Confirmed', 'Active', 'Closed']
def auto_close(s, pl):
    t = today()
    if s['status'] == 'Active' and pl and pl['autoClose'] and (s['exp'] < t or (pl['to'] and pl['to'] < t)):
        s['status'] = 'Closed'; return True
def run_billing():
    t = today(); plans = {p['id']: p for p in allc('plans')}; discs = allc('discounts')
    ex = {i['key'] for i in allc('invoices')}; T = tm(); created = 0
    for s in allc('subs'):
        pl = plans.get(s['plan']); ch = False; n = 0
        while pl and s['status'] == 'Active' and not s['paused'] and s['next'] <= t and s['next'] <= s['exp'] and n < 400:
            n += 1; key = s['id'] + '@' + s['next']
            if key not in ex:  # a billing period is never billed twice
                lines = [{**l, 'name': ''} for l in s['lines']]
                if pl['price'] > 0: lines.insert(0, {'prod': '', 'vi': -1, 'qty': 1, 'price': pl['price'], 'tax': '', 'name': 'Plan fee - ' + pl['name']})
                lines = named(lines); ds = apply_discounts(lines, discs, t)
                for d in ds: next(x for x in discs if x['id'] == d['id'])['used'] += 1
                days = int(s['terms'].split()[0]) if s['terms'][0].isdigit() else 0
                put('invoices', dict(id=uid(), no='INV-%05d' % nextno('inv'), key=key, sub=s['id'], cust=s['cust'], date=t, due=aD(s['next'], days),
                                     lines=lines, disc=ds, status='Draft', sent=False, **totals(lines, ds, T)))
                ex.add(key); created += 1
            s['next'] = adv(s['next'], pl['period']); ch = True
        if auto_close(s, pl): ch = True
        if ch: put('subs', s)
    for d in discs: put('discounts', d)
    return created

# ---------- enrichers ----------
def e_subs(items):
    U = {u['id']: u['name'] for u in allc('users')}; P = {p['id']: p for p in allc('plans')}; T = tm()
    return [{**s, 'lines': named(s['lines']), 'customer_name': U.get(s['cust'], '?'), 'plan_name': P.get(s['plan'], {}).get('name', '?'),
             'label': 'Paused' if s['paused'] and s['status'] == 'Active' else s['status'], **totals(s['lines'], (), T)} for s in items]
def e_inv(items):
    U = {u['id']: u['name'] for u in allc('users')}; pm = paidmap(); S = {s['id']: s['no'] for s in allc('subs')}
    return [{**i, 'customer_name': U.get(i['cust'], '?'), 'sub_no': S.get(i['sub'], ''), 'paid': round(pm.get(i['id'], 0), 2), 'balance': round(i['total'] - pm.get(i['id'], 0), 2),
             'label': dstatus(i, pm)} for i in items]
def e_pay(items):
    U = {u['id']: u['name'] for u in allc('users')}; I = {i['id']: i for i in allc('invoices')}
    return [{**p, 'invoice_no': I.get(p['inv'], {}).get('no', '?'), 'customer_name': U.get(I.get(p['inv'], {}).get('cust'), '?'), 'cust': I.get(p['inv'], {}).get('cust')} for p in items]
def paged(items, q):
    per = max(1, min(int(q.get('per', 15)), 100)); pg = max(0, int(q.get('page', 0)))
    return dict(items=items[pg * per:(pg + 1) * per], total=len(items), pages=max(1, -(-len(items) // per)))
def search(items, q, keys):
    s = (q.get('q') or '').lower()
    return [i for i in items if any(s in str(i.get(k, '')).lower() for k in keys)] if s else items

# ---------- validators for admin-managed data ----------
def clean(col, b, old=None):
    d = {'id': old['id'] if old else uid()}
    if col == 'products':
        vs = [{'attr': req(v, 'attr'), 'val': req(v, 'val'), 'extra': num(v, 'extra', -10**9, req=False)} for v in b.get('variants', [])]
        d.update(name=req(b, 'name'), type=str(b.get('type', '')), price=num(b, 'price'), cost=num(b, 'cost'), notes=str(b.get('notes', '')), variants=vs)
    elif col == 'plans':
        if b.get('period') not in PER: raise Err(400, 'Billing period must be daily, weekly, monthly or yearly.')
        if not isdate(b.get('from', '')): raise Err(400, 'Available-from date is required.')
        to = b.get('to') or ''
        if to and (not isdate(to) or to < b['from']): raise Err(400, 'Available-until must be after available-from.')
        d.update(name=req(b, 'name'), price=num(b, 'price'), period=b['period'], minQty=num(b, 'minQty', 1), **{'from': b['from'], 'to': to},
                 **{k: bool(b.get(k)) for k in ('autoClose', 'closable', 'pausable', 'renewable')})
    elif col == 'taxes': d.update(name=req(b, 'name'), rate=num(b, 'rate', 0, 100))
    elif col == 'discounts':
        if b.get('kind') not in ('fixed', 'percent') or b.get('scope') not in ('product', 'subscription'): raise Err(400, 'Choose a discount type and scope.')
        v = num(b, 'value', 0.0001, 100 if b['kind'] == 'percent' else None)
        if b['scope'] == 'product' and not getd('products', b.get('prod')): raise Err(400, 'Choose a product.')
        if not (isdate(b.get('from', '')) and isdate(b.get('to', '')) and b['to'] >= b['from']): raise Err(400, 'End date must be on or after the start date.')
        d.update(name=req(b, 'name'), kind=b['kind'], value=v, scope=b['scope'], prod=b.get('prod') if b['scope'] == 'product' else '', minPurchase=num(b, 'minPurchase', req=False),
                 minQty=num(b, 'minQty', req=False), limit=int(num(b, 'limit', req=False)), used=old['used'] if old else 0, **{'from': b['from'], 'to': b['to']})
    elif col == 'templates':
        if not getd('plans', b.get('plan')): raise Err(400, 'Choose a plan.')
        d.update(name=req(b, 'name'), plan=b['plan'], days=int(num(b, 'days', 1)), lines=[{k: l.get(k) for k in ('prod', 'vi', 'qty', 'tax')} for l in build_lines(b.get('lines'))])
    return d

# ---------- request handling ----------
def handle(m, p, q, b, u):
    a = p[0]; staff = u and u['role'] in ('admin', 'staff'); admin = u and u['role'] == 'admin'
    def need(ok, msg='You do not have access to this.'):
        if not ok: raise Err(403, msg)
    if a == 'signup' and m == 'POST':
        email = req(b, 'email').lower(); name = req(b, 'name')
        if not re.match(r'^\S+@\S+\.\S+$', email): raise Err(400, 'Enter a valid email.')
        if any(x['email'] == email for x in allc('users')): raise Err(409, 'That email already has an account.')
        e = pwerr(str(b.get('password', '')))
        if e: raise Err(400, e)
        nu = dict(id=uid(), email=email, name=name, role='customer', pw=hpw(b['password'])); put('users', nu); return new_session(nu)
    if a == 'login' and m == 'POST':
        us = [x for x in allc('users') if x['email'] == str(b.get('email', '')).strip().lower()]
        if not us or not chk(str(b.get('password', '')), us[0]['pw']): raise Err(401, 'Email or password is incorrect.')
        return new_session(us[0])
    if a == 'forgot' and m == 'POST':
        us = [x for x in allc('users') if x['email'] == str(b.get('email', '')).strip().lower()]
        if us:
            tok = secrets.token_urlsafe(24); put('resets', dict(id=tok, uid=us[0]['id'], exp=(dt.datetime.utcnow() + dt.timedelta(hours=1)).isoformat()))
            link = f"http://localhost:8000/?reset={tok}"; send_mail(us[0]['email'], 'Reset your Brightloop password', f'Open this link within an hour: {link}')
            return {'ok': True, 'dev_token': tok}
        raise Err(404, 'No account uses that email.')
    if a == 'reset' and m == 'POST':
        r = getd('resets', b.get('token'))
        if not r or r['exp'] < dt.datetime.utcnow().isoformat(): raise Err(400, 'This reset link is invalid or has expired.')
        e = pwerr(str(b.get('password', '')))
        if e: raise Err(400, e)
        us = getd('users', r['uid']); us['pw'] = hpw(b['password']); put('users', us)
        db.execute("delete from docs where col='resets' and id=?", (r['id'],)); return {'ok': True}
    if not u: raise Err(401, 'Please log in.')
    if a == 'me': return {'user': pub(u)}
    if a == 'logout':
        db.execute("delete from docs where col='sessions' and id=?", (b.get('_tok', ''),)); return {'ok': True}
    if a == 'lookups':
        need(staff)
        return dict(customers=[pub(x) for x in allc('users') if x['role'] == 'customer'], products=allc('products'), plans=allc('plans'), taxes=allc('taxes'), templates=named_t())
    if a == 'billing' and m == 'POST': need(staff); return {'created': run_billing()}
    if a == 'admin' and p[1] == 'demo':
        need(admin); plans = allc('plans'); prods = allc('products'); cs = [x for x in allc('users') if x['role'] == 'customer']; tx = allc('taxes')[0]['id']; t = today()
        for k in range(2000):
            pr = prods[k % 3]; put('subs', dict(id=uid(), no='SUB-%04d' % nextno('sub'), cust=cs[k % len(cs)]['id'], plan=plans[k % 2]['id'], start=aD(t, -(k % 60)), exp=aD(t, 300), terms='30 Days',
                status=['Active', 'Active', 'Confirmed', 'Closed', 'Quotation'][k % 5], paused=False, next=aD(t, -(k % 60)), lines=[dict(prod=pr['id'], vi=-1, qty=1 + k % 7, price=pr['price'], tax=tx)]))
        return {'ok': True}
    if a == 'reports': need(staff); return summary(q)
    if a == 'portal' and p[1] == 'pay' and m == 'POST':
        i = getd('invoices', p[2]); need(i and i['cust'] == u['id'], 'Invoice not found.'); return pay({'inv': i['id'], 'method': 'Online', 'amt': i['total'] - paidmap().get(i['id'], 0), 'date': today(), 'note': 'Paid in portal'})
    if a in ('products', 'plans', 'taxes', 'discounts', 'templates'):
        need(staff)
        if m == 'GET': return paged(search(sorted(named_t() if a == 'templates' else allc(a), key=lambda x: x['name']), q, ['name']), q)
        need(admin, 'Only the admin can change this.')
        if m == 'POST': d = clean(a, b); put(a, d); return d
        if m == 'PUT': old = getd(a, p[1]); need(old, 'Not found.'); d = clean(a, b, old); put(a, d); return d
    if a == 'users':
        need(staff)
        if m == 'GET':
            role = q.get('role', 'customer'); need(role == 'customer' or admin); S = {}
            for s in allc('subs'): S[s['cust']] = S.get(s['cust'], 0) + 1
            items = [{**pub(x), 'subs': S.get(x['id'], 0)} for x in allc('users') if x['role'] == role]; return paged(search(items, q, ['name', 'email']), q)
        role = b.get('role', 'customer'); need(role == 'customer' or admin, 'Only the admin can add staff.')
        if role not in ('customer', 'staff'): raise Err(400, 'Invalid role.')
        email = req(b, 'email').lower()
        if not re.match(r'^\S+@\S+\.\S+$', email): raise Err(400, 'Enter a valid email.')
        if any(x['email'] == email for x in allc('users')): raise Err(409, 'That email already has an account.')
        e = pwerr(str(b.get('password', '')))
        if e: raise Err(400, e)
        nu = dict(id=uid(), email=email, name=req(b, 'name'), role=role, pw=hpw(b['password'])); put('users', nu); return pub(nu)
    if a == 'subs': return subs_api(m, p, q, b, u, staff)
    if a == 'invoices': return inv_api(m, p, q, b, u, staff)
    if a == 'payments':
        if m == 'GET':
            items = e_pay(sorted(allc('payments'), key=lambda x: x['date'], reverse=True))
            if not staff: items = [x for x in items if x['cust'] == u['id']]
            return paged(search(items, q, ['invoice_no', 'customer_name', 'method', 'note']), q)
        need(staff); return pay(b)
    raise Err(404, 'Not found.')

def named_t(): return [{**t, 'lines': named(t['lines']), 'plan_name': (getd('plans', t['plan']) or {}).get('name', '?')} for t in allc('templates')]
def new_session(u):
    tok = secrets.token_urlsafe(24); put('sessions', {'id': tok, 'uid': u['id']}); return {'token': tok, 'user': pub(u)}

def subs_api(m, p, q, b, u, staff):
    P = {x['id']: x for x in allc('plans')}
    for s in allc('subs'):  # plans that end close their subscriptions on their own
        if auto_close(s, P.get(s['plan'])): put('subs', s)
    if m == 'GET' and len(p) == 1:
        items = sorted(allc('subs'), key=lambda s: s['no'])
        if not staff: items = [s for s in items if s['cust'] == u['id']]
        if q.get('status'): items = [s for s in items if s['status'] == q['status']]
        return paged(search(e_subs(items), q, ['no', 'customer_name', 'plan_name']), q)
    s = getd('subs', p[1]) if len(p) > 1 else None
    if m == 'GET': 
        if not s or (not staff and s['cust'] != u['id']): raise Err(404, 'Subscription not found.')
        return {**e_subs([s])[0], 'plan': P.get(s['plan'])}
    if m == 'POST' and len(p) == 1 or (len(p) == 2 and p[1] == 'from-template'):
        if not staff: raise Err(403, 'You do not have access to this.')
        c = getd('users', b.get('cust'))
        if not c or c['role'] != 'customer': raise Err(400, 'Choose a customer.')
        if len(p) == 2:
            t = getd('templates', b.get('template'))
            if not t: raise Err(400, 'Choose a template.')
            b = dict(cust=c['id'], plan=t['plan'], start=today(), exp=aM(today(), 12), terms='30 Days', lines=t['lines'], valid=aD(today(), t['days'])); status = 'Quotation'
        else: status = 'Draft'
        pl = P.get(b.get('plan'))
        if not pl: raise Err(400, 'Choose a plan.')
        if not (isdate(b.get('start', '')) and isdate(b.get('exp', '')) and b['exp'] > b['start']): raise Err(400, 'Expiry must be after the start date.')
        if b['start'] < pl['from'] or (pl['to'] and b['start'] > pl['to']): raise Err(400, f"This plan is only available from {pl['from']}" + (f" to {pl['to']}." if pl['to'] else '.'))
        if b.get('terms') not in ('Immediate', '15 Days', '30 Days'): raise Err(400, 'Choose payment terms.')
        lines = build_lines(b['lines'])
        if sum(l['qty'] for l in lines) < pl['minQty']: raise Err(400, f"This plan needs a minimum quantity of {int(pl['minQty'])}.")
        d = dict(id=uid(), no='SUB-%04d' % nextno('sub'), cust=c['id'], plan=pl['id'], start=b['start'], exp=b['exp'], terms=b['terms'], status=status, paused=False, next=b['start'], lines=lines)
        if b.get('valid'): d['valid'] = b['valid']
        put('subs', d); return d
    if not s or (not staff and s['cust'] != u['id']): raise Err(404, 'Subscription not found.')
    pl = P[s['plan']]; act = p[2] if len(p) > 2 else ''
    if act == 'lines':
        if not staff or s['status'] in ('Active', 'Closed'): raise Err(403, 'Lines can only be added before activation.')
        s['lines'] += build_lines([b]); put('subs', s); return s
    if act == 'status':
        new = b.get('status'); cur = s['status']
        if new == 'Closed' and cur == 'Active':
            if not staff and not pl['closable']: raise Err(403, 'This plan cannot be closed early.')
        elif not staff or new not in FLOW or FLOW.index(new) != FLOW.index(cur) + 1: raise Err(400, f'A {cur} subscription cannot move to {new}.')
        s['status'] = new
        if new == 'Active': s['next'] = max(s['next'], s['start']) if False else s['start'] if s['next'] < s['start'] else s['next']
        put('subs', s); return s
    if act == 'pause':
        if s['status'] != 'Active' or not pl['pausable']: raise Err(403, 'This plan cannot be paused.')
        s['paused'] = not s['paused']; put('subs', s); return s
    if act == 'renew':
        if not pl['renewable'] or s['status'] not in ('Active', 'Closed'): raise Err(403, 'This plan cannot be renewed.')
        s['exp'] = aM(s['exp'], 12); s['status'] = 'Active'; put('subs', s); return s
    raise Err(404, 'Not found.')

def inv_api(m, p, q, b, u, staff):
    pm = paidmap()
    if m == 'GET' and len(p) == 1:
        items = allc('invoices')
        if not staff: items = [i for i in items if i['cust'] == u['id'] and i['status'] not in ('Draft', 'Cancelled')]
        items = e_inv(sorted(items, key=lambda i: i['no'], reverse=True))
        if q.get('status'): items = [i for i in items if i['label'] == q['status']]
        if q.get('open'): items = [i for i in items if i['status'] == 'Confirmed' and i['balance'] > 0.005]
        return paged(search(items, q, ['no', 'customer_name']), q)
    i = getd('invoices', p[1])
    if not i or (not staff and (i['cust'] != u['id'] or i['status'] in ('Draft', 'Cancelled'))): raise Err(404, 'Invoice not found.')
    if m == 'GET': return e_inv([i])[0]
    if not staff: raise Err(403, 'You do not have access to this.')
    act = p[2] if len(p) > 2 else ''
    if act == 'status':
        new = b.get('status')
        if new == 'Confirmed' and i['status'] == 'Draft': i['status'] = 'Confirmed'
        elif new == 'Cancelled' and i['status'] in ('Draft', 'Confirmed') and not pm.get(i['id']): i['status'] = 'Cancelled'
        else: raise Err(400, f"A {i['status']} invoice cannot be {new.lower()}.")
        put('invoices', i); return i
    if act == 'send':
        if i['status'] not in ('Confirmed', 'Paid'): raise Err(400, 'Confirm the invoice before sending it.')
        c = getd('users', i['cust']); i['sent'] = True; put('invoices', i)
        send_mail(c['email'], f"Invoice {i['no']}", f"Hello {c['name']}, invoice {i['no']} for {i['total']} is due {i['due']}."); return {'ok': True, 'to': c['email']}
    raise Err(404, 'Not found.')

def pay(b):
    i = getd('invoices', b.get('inv'))
    if not i: raise Err(400, 'Choose an invoice.')
    if i['status'] != 'Confirmed': raise Err(400, 'Only confirmed invoices can receive payments.')
    if b.get('method') not in ('Bank transfer', 'Card', 'UPI', 'Cash', 'Cheque', 'Online'): raise Err(400, 'Choose a payment method.')
    if not isdate(b.get('date', '')): raise Err(400, 'Enter a payment date.')
    bal = i['total'] - paidmap().get(i['id'], 0); amt = num(b, 'amt', 0.01)
    if amt > bal + 0.005: raise Err(400, f'Amount cannot be more than the balance of {bal:.2f}.')
    put('payments', dict(id=uid(), inv=i['id'], method=b['method'], amt=round(amt, 2), date=b['date'], note=str(b.get('note', ''))[:300]))
    if bal - amt <= 0.005: i['status'] = 'Paid'; put('invoices', i)
    return {'ok': True}

def summary(q):
    f, t = q.get('from') or '', q.get('to') or '9999-12-31'; subs = allc('subs'); P = {x['id']: x for x in allc('plans')}; pm = paidmap(); T = tm()
    inv = [i for i in allc('invoices') if i['status'] != 'Cancelled']
    mrr = sum((totals(s['lines'], (), T)['subtotal'] + P[s['plan']]['price']) * PER[P[s['plan']]['period']] for s in subs if s['status'] == 'Active' and s['plan'] in P)
    od = [i for i in inv if dstatus(i, pm) == 'Overdue' and f <= i['due'] <= t]; counts = {}
    for s in subs: counts[s['status']] = counts.get(s['status'], 0) + 1
    return dict(active=counts.get('Active', 0), counts=counts, mrr=round(mrr, 2), revenue=round(sum(x['amt'] for x in allc('payments') if f <= x['date'] <= t), 2),
                owed=round(sum(i['total'] - pm.get(i['id'], 0) for i in inv if i['status'] == 'Confirmed'), 2), overdue_count=len(od), overdue=e_inv(sorted(od, key=lambda i: i['due'])[:50]))

def send_mail(to, subject, body):
    print(f'[mail] to={to} subject={subject}\n       {body}')
    h = os.environ.get('SMTP_HOST')
    if not h: return
    try:
        msg = EmailMessage(); msg['To'], msg['Subject'], msg['From'] = to, subject, os.environ.get('SMTP_FROM', 'billing@brightloop.example'); msg.set_content(body)
        with smtplib.SMTP(h, int(os.environ.get('SMTP_PORT', 587))) as s:
            s.starttls(); s.login(os.environ['SMTP_USER'], os.environ['SMTP_PASS']); s.send_message(msg)
    except Exception as e: print('[mail] failed:', e)

def seed():
    if allc('users'): return
    t = today(); tx = uid(); p1, p2, p3 = uid(), uid(), uid(); pl1, pl2, pl3 = uid(), uid(), uid(); c1, c2 = uid(), uid()
    for r, n, e, pw in (('admin', 'Asha Admin', 'admin@brightloop.com', 'Admin@12345'), ('staff', 'Sam Staff', 'staff@brightloop.com', 'Staff@12345'),
                        ('customer', 'Corner Shop Ltd', 'shop@example.com', 'Shop@12345'), ('customer', 'Megacorp Inc', 'big@example.com', 'Big@123456')):
        put('users', dict(id={'shop@example.com': c1, 'big@example.com': c2}.get(e, uid()), email=e, name=n, role=r, pw=hpw(pw)))
    put('taxes', dict(id=tx, name='GST 18%', rate=18)); put('taxes', dict(id=uid(), name='GST 5%', rate=5))
    put('products', dict(id=p1, name='Brightloop ERP', type='Software', price=2000, cost=900, notes='Core suite', variants=[dict(attr='Brand', val='Odoo', extra=560), dict(attr='Brand', val='Native', extra=0)]))
    put('products', dict(id=p2, name='Extra Seat', type='Add-on', price=300, cost=80, notes='Per user', variants=[])); put('products', dict(id=p3, name='Priority Support', type='Add-on', price=1200, cost=500, notes='24x7', variants=[]))
    for i, n, pr, per, mq, to, fl in ((pl1, 'Monthly Standard', 0, 'monthly', 1, '', (1, 0, 1, 0)), (pl2, 'Yearly Enterprise', 5000, 'yearly', 5, '', (0, 1, 0, 1)), (pl3, 'Weekly Trial', 0, 'weekly', 1, '2030-12-31', (1, 0, 1, 0))):
        put('plans', dict(id=i, name=n, price=pr, period=per, minQty=mq, to=to, autoClose=bool(fl[0]), closable=bool(fl[1]) or i != pl3, pausable=bool(fl[2]), renewable=bool(fl[3]), **{'from': '2024-01-01'}))
    put('templates', dict(id=uid(), name='Enterprise starter pack', plan=pl2, days=30, lines=[dict(prod=p1, vi=0, qty=10, tax=tx), dict(prod=p2, vi=-1, qty=10, tax=tx)]))
    put('discounts', dict(id=uid(), name='Volume seats 10%', kind='percent', value=10, scope='product', prod=p2, minPurchase=0, minQty=5, limit=0, used=0, **{'from': aD(t, -60), 'to': aD(t, 300)}))
    put('subs', dict(id=uid(), no='SUB-%04d' % nextno('sub'), cust=c1, plan=pl1, start=aD(t, -65), exp=aD(t, 300), terms='15 Days', status='Active', paused=False, next=aD(t, -5), lines=[dict(prod=p1, vi=1, qty=2, price=2000, tax=tx)]))
    put('subs', dict(id=uid(), no='SUB-%04d' % nextno('sub'), cust=c2, plan=pl2, start=aD(t, -20), exp=aD(t, 345), terms='30 Days', status='Active', paused=False, next=aD(t, -20),
                     lines=[dict(prod=p1, vi=0, qty=10, price=2560, tax=tx), dict(prod=p2, vi=-1, qty=10, price=300, tax=tx)]))
    db.commit()

class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def send(self, code, obj, ctype='application/json'):
        raw = obj if isinstance(obj, bytes) else json.dumps(obj).encode()
        self.send_response(code); self.send_header('Content-Type', ctype); self.send_header('Content-Length', str(len(raw))); self.end_headers(); self.wfile.write(raw)
    def static(self, path):
        f = os.path.realpath(os.path.join(WEB, path.lstrip('/') or 'index.html'))
        if not f.startswith(WEB) or not os.path.isfile(f): f = os.path.join(WEB, 'index.html')
        self.send(200, open(f, 'rb').read(), (mimetypes.guess_type(f)[0] or 'text/plain') + '; charset=utf-8')
    def go(self, m):
        u = urllib.parse.urlparse(self.path)
        if not u.path.startswith('/api/'): return self.static(u.path) if m == 'GET' else self.send(405, {'error': 'Method not allowed'})
        q = {k: v[0] for k, v in urllib.parse.parse_qs(u.query).items()}; b = {}
        try:
            n = int(self.headers.get('Content-Length') or 0)
            if n: b = json.loads(self.rfile.read(n))
            tok = (self.headers.get('Authorization') or '')[7:]; b['_tok'] = tok if isinstance(b, dict) else ''
            with LOCK:
                s = getd('sessions', tok) if tok else None; user = getd('users', s['uid']) if s else None
                res = handle(m, [x for x in u.path[5:].split('/') if x], q, b, user); db.commit()
            self.send(200, res)
        except Err as e: db.rollback(); self.send(e.code, {'error': e.msg})
        except (ValueError, KeyError, TypeError) as e: db.rollback(); self.send(400, {'error': 'Invalid request: ' + str(e)})
        except Exception as e: db.rollback(); print('error', repr(e)); self.send(500, {'error': 'Server error.'})
    do_GET = lambda s: s.go('GET'); do_POST = lambda s: s.go('POST'); do_PUT = lambda s: s.go('PUT')

if __name__ == '__main__':
    seed(); port = int(os.environ.get('PORT', 8000))
    print(f'Brightloop running at http://localhost:{port}')
    ThreadingHTTPServer(('', port), H).serve_forever()
