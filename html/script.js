// ページ上の全ての block-header をフラット配列にする
const allHeaders = Array.from(document.querySelectorAll('.block-header'));
let selectedIndex = 0;

// 初期選択
if (allHeaders.length > 0) {
  allHeaders[selectedIndex].classList.add('selected');
}

document.addEventListener('click', (e) => {
  if (e.target.matches('.toggle')) {
    const btn = e.target;
    const header = btn.closest('.block-header');
    if (!header) return;
    const content = header.nextElementSibling;
    if (!content || !content.classList.contains('block-content')) return;
    content.classList.toggle('collapsed');
    btn.textContent = content.classList.contains('collapsed') ? '▶' : '▼';
    MathJax.typesetPromise();
  }
  const header = e.target.closest('.block-header');
  if (header) {
    // 前の選択を解除
    allHeaders.forEach(h => h.classList.remove('selected'));
    header.classList.add('selected');

    // 配列のインデックスを同期
    selectedIndex = allHeaders.indexOf(header);

    // infoPanel 更新
    const context_vars = header.nextElementSibling.innerHTML;
    const context_formulas = header.nextElementSibling.nextElementSibling.innerHTML;
    infoContent.innerHTML = `Clicked line: ${header.innerHTML}<br>context.vars: ${context_vars}<br>context.formulas: ${context_formulas}`;
    MathJax.typesetPromise();
  }
});

document.addEventListener('keydown', (e) => {
  if (e.key !== 'ArrowDown' && e.key !== 'ArrowUp') return;
  e.preventDefault(); // スクロールを止める

  if (allHeaders.length === 0) return;

  // 前の選択を解除
  allHeaders[selectedIndex].classList.remove('selected');

  if (e.key === 'ArrowDown') {
    selectedIndex = Math.min(selectedIndex + 1, allHeaders.length - 1);
  } else if (e.key === 'ArrowUp') {
    selectedIndex = Math.max(selectedIndex - 1, 0);
  }

  const header = allHeaders[selectedIndex];
  header.classList.add('selected');
  header.scrollIntoView({ behavior: 'smooth', block: 'center' });

  // infoPanel 更新
  const context_vars = header.nextElementSibling.innerHTML;
  const context_formulas = header.nextElementSibling.nextElementSibling.innerHTML;
  infoContent.innerHTML = `Selected line: ${header.innerHTML}<br>context.vars: ${context_vars}<br>context.formulas: ${context_formulas}`;
  MathJax.typesetPromise();
});

document.getElementById('expandAll').addEventListener('click', () => {
  document.querySelectorAll('.block-content').forEach(c => c.classList.remove('collapsed'));
  document.querySelectorAll('.toggle').forEach(b => b.textContent='▼');
  MathJax.typesetPromise();
});
document.getElementById('collapseAll').addEventListener('click', () => {
  document.querySelectorAll('.block-content').forEach(c => c.classList.add('collapsed'));
  document.querySelectorAll('.toggle').forEach(b => b.textContent='▶');
});
