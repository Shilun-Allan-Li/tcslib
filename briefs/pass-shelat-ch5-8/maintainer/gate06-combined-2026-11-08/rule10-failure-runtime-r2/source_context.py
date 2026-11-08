"""Own conservative source index. No Lean execution or semantic-name resolution.

Every file/prefix/import closure remains an exact immutable context witness even
when lexical declaration mapping is ambiguous. No classification is a waiver.
"""
import bisect,hashlib,json,re
DECLS={'theorem','lemma','def','abbrev','opaque','axiom','instance','structure','inductive','class','example'}
DATA=DECLS-{'theorem','lemma','example'}
MODIFIERS={'private','protected','noncomputable','nonrec','unsafe','partial','public','local','scoped'}
PREFIX=r'(?:(?:private|protected|noncomputable|nonrec|unsafe|partial|public|local|scoped)\s+)*'
DECL=re.compile(r'^'+PREFIX+r'(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|instance|structure|inductive|class|example)\b')
COMMAND=re.compile(r'^(?:(?:noncomputable|public|private)\s+section|public\s+import|namespace|section|end|import|prelude|module|open|export|attribute|variable|variables|include|omit|set_option|local|scoped|syntax|macro|elab|initialize|builtin_initialize|mutual|notation|infix[lr]?|prefix|postfix|declare_syntax_cat|register_option|#\w+)\b')

def sha(b):return hashlib.sha256(b.encode() if isinstance(b,str) else b).hexdigest()
def canonical(value):return json.dumps(value,ensure_ascii=False,sort_keys=True,separators=(',',':'))

def lex(text):
    """Keep positions; distinguish comments from literal/quoted-identifier data."""
    comments=[];struct=list(text);i=0
    def blank(a,b):
        for k in range(a,b):
            if struct[k] not in '\r\n':struct[k]=' '
    while i<len(text):
        if text.startswith('--',i):
            end=text.find('\n',i);end=len(text) if end<0 else end;comments.append((i,end));blank(i,end);i=end
        elif text.startswith('/-',i):
            begin=i;depth=1;i+=2
            while i<len(text) and depth:
                if text.startswith('/-',i):depth+=1;i+=2
                elif text.startswith('-/',i):depth-=1;i+=2
                else:i+=1
            if depth:raise ValueError('unclosed nested comment')
            comments.append((begin,i));blank(begin,i)
        else:
            raw=re.match(r'r(#+)?"',text[i:]) if text[i]=='r' else None
            if raw:
                fence='"'+(raw[1] or '');end=text.find(fence,i+len(raw[0]))
                if end<0:raise ValueError('unclosed raw string')
                end+=len(fence);blank(i,end);i=end
            elif text[i] in ('"','«'):
                close='"' if text[i]=='"' else '»';end=i+1
                while end<len(text):
                    if close=='"' and text[end]=='\\':end+=2;continue
                    if text[end]==close:break
                    end+=1
                if end>=len(text):raise ValueError('unclosed string/quoted identifier')
                end+=1;blank(i,end);i=end
            elif text[i]=="'" and (c:=re.match(r"'(?:[^'\\\r\n]|\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.))'",text[i:])):
                blank(i,i+len(c[0]));i+=len(c[0])
            else:i+=1
    cm=list(text)
    for a,b in comments:
        for k in range(a,b):
            if cm[k] not in '\r\n':cm[k]=' '
    return ''.join(struct),''.join(cm),comments

def code(text):
    _,_,spans=lex(text);out=[];at=0
    for a,b in spans:out.append(text[at:a]);at=b
    out.append(text[at:]);return ''.join(out)

def source_name(text):
    """A source identifier only; quotes preserve component boundaries. No numeric guessing."""
    parts=[];i=0
    while i<len(text):
        if text[i]=='«':
            j=text.find('»',i+1)
            if j<0:return None,None
            parts.append(text[i+1:j]);i=j+1
        else:
            m=re.match(r"[^\s.(){}\[\]:,;=]+",text[i:])
            if not m:break
            parts.append(m[0]);i+=len(m[0])
        if i<len(text) and text[i]=='.':
            if text.startswith('.{',i):break
            i+=1
            if i==len(text) or text[i].isspace():return None,None
            continue
        break
    if not parts or (i and text[i-1]=='.'):return None,None
    return text[:i],parts

def _equation_clause(masked,at):
    """A line-leading clause bar with a top-level arrow, not absolute-value bars.

    Ambiguous/multiline alternatives are not guessed. Match expressions in a
    type still receive the separate unresolved-header warning below.
    """
    if masked[masked.rfind('\n',0,at)+1:at].strip():return False
    stop=masked.find('\n',at);stop=len(masked) if stop<0 else stop;depth=0
    for i in range(at+1,stop):
        ch=masked[i]
        if ch in '([{':depth+=1
        elif ch in ')]}':depth=max(0,depth-1)
        elif depth==0:
            if ch=='|':return False
            if masked.startswith('=>',i):return True
    return False

def body_split(masked):
    depth=0;i=0
    while i<len(masked):
        c=masked[i]
        if c in '([{':depth+=1
        elif c in ')]}':depth=max(0,depth-1)
        elif depth==0:
            if masked.startswith(':=',i):return i,'assignment'
            if re.match(r'where\b',masked[i:]) and (i==0 or not(masked[i-1].isalnum() or masked[i-1]=='_')):return i,'where'
            if c=='|' and _equation_clause(masked,i):return i,'equations'
        i+=1
    return len(masked),'bodyless_or_unparsed'

def _space(masked,at):
    while at<len(masked) and masked[at].isspace():at+=1
    return at

def _balanced(masked,at):
    """End of one balanced group; quoted/literal/comment interiors are masked."""
    pairs={'(':')','[':']','{':'}'};stack=[]
    for i in range(at,len(masked)):
        ch=masked[i]
        if ch in pairs:stack.append(pairs[ch])
        elif ch in ')]}':
            if not stack or stack.pop()!=ch:return None
            if not stack:return i+1
    return None

def _declaration_prefix(masked,at):
    """Consume attributes AND modifiers before the actual declaration keyword.

    A malformed/unsupported attribute prefix is an unresolved event of its own.
    It is never carried forward to the next unrelated plain declaration.
    """
    begin=at;attrs=[];modifiers=[]
    while True:
        at=_space(masked,at)
        if masked.startswith('@[',at):
            end=_balanced(masked,at+1)
            if end is None:return {'kind':'unresolved-prefix','keyword_at':begin,'after_keyword':at+2,'attrs':attrs,'modifiers':modifiers,'issue':'UNBALANCED_ATTRIBUTE_PREFIX','consumed_until':at+2}
            attrs.append((at,end));at=end;continue
        word=re.match(r'[A-Za-z_][A-Za-z_0-9]*\b',masked[at:])
        if word and word[0] in MODIFIERS:
            modifiers.append(word[0]);at+=len(word[0]);continue
        if word and word[0] in DECLS:
            return {'kind':word[0],'keyword_at':at,'after_keyword':at+len(word[0]),'attrs':attrs,'modifiers':modifiers,'consumed_until':at+len(word[0])}
        if attrs:
            return {'kind':'unresolved-prefix','keyword_at':begin,'after_keyword':at,'attrs':attrs,'modifiers':modifiers,'issue':'ATTRIBUTE_PREFIX_NOT_FOLLOWED_BY_KNOWN_DECLARATION','consumed_until':at}
        return None

def _top_level_type_risk(masked):
    """Do not guess a header/body split for unparenthesized let/match types."""
    depth=0
    for i,ch in enumerate(masked):
        if ch in '([{':depth+=1
        elif ch in ')]}':depth=max(0,depth-1)
        elif depth==0 and re.match(r'(?:let|match)\b',masked[i:]) and (i==0 or not(masked[i-1].isalnum() or masked[i-1]=='_')):return True
    return False

def mapping_safe(unit):
    return bool(unit['kind'] in DECLS and unit.get('canonical_parts') is not None and not unit.get('lexical_boundaries_need_review') and not unit.get('namespace_context_ambiguous'))

def source_key_matches(unit,key):
    """Historical source-key agreement only; never an elaborated Name assertion."""
    if not mapping_safe(unit):return False
    name,parts=source_name(key)
    if name!=key or parts is None:return False
    if key.startswith('_root_.'):parts=parts[1:]
    return parts==unit['canonical_parts']

def parse(text):
    structural,cm,comments=lex(text)
    lines=text.splitlines(keepends=True);ml=structural.splitlines(keepends=True);cl=cm.splitlines(keepends=True)
    offsets=[];at=0
    for line in lines:offsets.append(at);at+=len(line)
    line_of=lambda pos:bisect.bisect_right(offsets,pos)
    events=[];indented=[];issues=[];consumed_until=0;unbalanced_attribute_lines=[]
    for i,masked in enumerate(ml):
        begin=offsets[i];st=masked.rstrip('\r\n')
        if begin<consumed_until or not st.strip():continue
        indent=len(st)-len(st.lstrip());candidate=begin+indent
        pref=_declaration_prefix(structural,candidate)
        if indent:
            if pref is not None:
                indented.append(i+1)
                events.append({'line':i+1,'start_line':i+1,'kind':'unresolved-indented-declaration','keyword_at':candidate,'after_keyword':candidate,'attrs':[],'modifiers':[],'issue':'INDENTED_DECLARATION_OR_NESTED_HELPER_UNRESOLVED'})
                consumed_until=pref['consumed_until']
            continue
        if pref is not None:
            ev={**pref,'start_line':i+1,'line':line_of(pref['keyword_at'])}
            if pref.get('issue')=='UNBALANCED_ATTRIBUTE_PREFIX':unbalanced_attribute_lines.append(i+1)
            consumed_until=pref['consumed_until']
            events.append(ev)
        elif COMMAND.match(st):
            events.append({'line':i+1,'start_line':i+1,'kind':'source-command','keyword_at':begin,'after_keyword':begin,'attrs':[],'modifiers':[]})
    frames=[];ns=[];bindings=[];units=[];namespace_ambiguous=False
    for k,ev in enumerate(events):
        line=ev['line'];start=ev['start_line'];end=events[k+1]['start_line']-1 if k+1<len(events) else len(lines)
        while end>=line and not cl[end-1].strip():end-=1
        end=max(end,line);begin=offsets[start-1];finish=offsets[end] if end<len(offsets) else len(text)
        raw=text[begin:finish];masked=structural[begin:finish]
        kind=ev['kind'];original=cl[start-1].strip();name=None;parts=None
        if kind in DECLS and kind!='example':
            nameat=_space(cm,ev['after_keyword'])
            if kind=='instance' and structural[nameat:nameat+1]=='(':
                stop=_balanced(structural,nameat)
                # Priority binders precede either a named or an anonymous instance.
                if stop is not None and re.match(r'\(\s*priority\b',cm[nameat:stop]):nameat=_space(cm,stop)
            suffix=cm[nameat:finish]
            if not (kind=='instance' and suffix.startswith((':','(','{','['))):name,parts=source_name(suffix)
        qparts=(parts[1:] if name and name.startswith('_root_.') else ns+(parts or [])) if parts else None
        pos,form=body_split(masked) if kind in DECLS else (len(masked),'command')
        header=raw[:pos];body=raw[pos:];warnings=[]
        if ev.get('issue'):warnings.append(ev['issue'])
        if any(a<start for a in unbalanced_attribute_lines):warnings.append('PRECEDING_UNBALANCED_ATTRIBUTE_UNRESOLVED')
        if k+1<len(events) and events[k+1]['kind']=='unresolved-indented-declaration' and kind in DECLS:warnings.append('NEXT_INDENTED_EVENT_MAY_BE_NESTED_IN_THIS_DECLARATION')
        if kind in {'theorem','lemma','def','abbrev'} and form=='bodyless_or_unparsed':warnings.append('NO_RECOGNIZED_BODY_BOUNDARY')
        if kind in DECLS and _top_level_type_risk(masked[:pos]):warnings.append('HEADER_LET_OR_MATCH_BOUNDARY_UNRESOLVED')
        if kind in DECLS and kind not in {'instance','example'} and parts is None:warnings.append('DECLARED_NAME_UNRESOLVED')
        if any(f['kind']=='mutual' for f in frames):warnings.append('MUTUAL_DECLARATION_CONTEXT_UNRESOLVED')
        prefix=text[:begin];attr_lines=sorted({line_of(p) for a,b in ev['attrs'] for p in range(a,b) if p==a or text[p-1]=='\n'})
        unit={'id':f'{start}:{end}:{sha(raw)}','kind':kind,'source_name':name,'canonical_parts':qparts,'canonical':'.'.join(qparts) if qparts else None,
            'start_line':start,'declaration_line':line,'end_line':end,'char_start':begin,'char_end':finish,'declaration_keyword_char_start':ev['keyword_at'],
            'raw_sha256':sha(raw),'code_sha256':sha(code(raw)),'declaration_raw_sha256':sha(raw),
            'header_raw_sha256':sha(header),'header_code_sha256':sha(code(header)),
            'body_raw_sha256':sha(body),'body_code_sha256':sha(code(body)),'body_form':form,
            'namespace_parts':ns[:],'scope_stack':[{'kind':f['kind'],'name':f['name']} for f in frames],
            'binding_trace_sha256':sha(canonical(bindings)),'binding_trace':bindings[:],
            'complete_prefix_raw_sha256':sha(prefix),'complete_prefix_code_sha256':sha(code(prefix)),
            'prefix_char_end':begin,'attribute_lines':attr_lines,'attribute_char_spans':ev['attrs'],'modifiers':ev['modifiers'],
            'name_basis':'LEXICAL_SOURCE_SPELLING_NOT_ACTUAL_LEAN_NAME','lexical_boundaries_need_review':bool(warnings),
            'mapping_warnings':warnings,'namespace_context_ambiguous':namespace_ambiguous}
        units.append(unit)
        for warning in warnings:issues.append({'line':start,'end_line':end,'issue':warning})
        if kind=='source-command':
            if original.startswith('namespace '):
                sn,sp=source_name(original[len('namespace '):]);frames.append({'kind':'namespace','name':sn,'oldns':ns[:]})
                if sp is None:namespace_ambiguous=True
                else:ns=sp[1:] if sn.startswith('_root_.') else ns+sp
            elif re.match(r'^(?:(?:noncomputable|public|private)\s+)?section\b',original):frames.append({'kind':'section','name':original,'oldns':ns[:]})
            elif original=='mutual':frames.append({'kind':'mutual','name':'mutual','oldns':ns[:]})
            elif re.match(r'^end\b',original):
                if frames:ns=frames.pop()['oldns']
                else:
                    namespace_ambiguous=True;unit['lexical_boundaries_need_review']=True;unit['mapping_warnings'].append('UNMATCHED_END')
            # Retain ALL preceding commands, including global attributes inside ended
            # sections. This trace is an over-approximation, not an effect interpreter.
            bindings.append({'kind':'source-command','source':code(raw)})
    return {'parser_version':'R2_ATTRIBUTE_AWARE_FAIL_CLOSED','units':units,'indented_declaration_lines':indented,'unclosed_scope_count':len(frames),
        'mapping_issues':issues,'code_sha256':sha(code(text)),'raw_sha256':sha(text),'line_count':len(lines),
        'limit':'Lexical source envelopes only. Unknown/indented/mutual/header boundaries remain unresolved; full file/prefix/closure witnesses are authoritative. No elaboration, actual-Name or semantic command/dependency resolution.'}

def imports(text):
    st,_,_=lex(text);names=[];closed=False
    for line in st.splitlines():
        s=line.strip()
        if not s:continue
        mt=re.fullmatch(r'(?:public\s+)?import\s+(.+)',s)
        if mt:
            if closed:raise ValueError('late import')
            names.extend(mt[1].split())
        elif s=='prelude' or s=='module':continue
        else:closed=True
    return names

def select_unit(index,line):
    return [u for u in index['units'] if u['start_line']<=line<=u['end_line']]

def match_unit(index,unit):
    if not mapping_safe(unit):return []
    return [u for u in index['units'] if mapping_safe(u) and u['kind']==unit['kind'] and u['canonical_parts']==unit['canonical_parts']]

def actual_key(identity):
    parts=identity['components']
    for tag,value in parts:
        if tag not in ('str','num') or not isinstance(value,str):raise ValueError('bad actual Name component')
        if tag=='num' and not re.fullmatch(r'0|[1-9][0-9]*',value):raise ValueError('bad numeric Name component')
    return canonical(parts)

def user_parts(parts):
    """Separate source-correspondence view, following Lean.PrivateName; never identity normalization."""
    if parts and parts[0]==['str','_private']:
        for i,(tag,value) in enumerate(parts[1:],1):
            if tag=='num':
                if value=='0' and all(t=='str' for t,v in parts[:i]):return parts[i+1:]
                break
    return parts
