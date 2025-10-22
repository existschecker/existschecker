let selectedHeader = document.querySelector('.block-header');
if (selectedHeader) {
  selectedHeader.classList.add('selected');
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
    if (selectedHeader) {
      selectedHeader.classList.remove('selected');
    }
    selectedHeader = header;
    selectedHeader.classList.add('selected');
    const context_vars = header.nextElementSibling.innerHTML;
    const context_formulas = header.nextElementSibling.nextElementSibling.innerHTML;
    infoContent.innerHTML = `Clicked line: ${header.innerHTML}<br>context.vars: ${context_vars}<br>context.formulas: ${context_formulas}`;
    MathJax.typesetPromise();
  }
});

document.addEventListener('keydown', (e) => {
  if (e.key !== 'ArrowDown' && e.key !== 'ArrowUp') return;
  e.preventDefault(); // スクロールを止める

  if (!selectedHeader) return;

  let nextHeader = null;
  if (e.key === 'ArrowDown') {
    const nextBlock = selectedHeader.closest('.block').nextElementSibling;
    if (nextBlock) nextHeader = nextBlock.querySelector('.block-header');
  } else if (e.key === 'ArrowUp') {
    const prevBlock = selectedHeader.closest('.block').previousElementSibling;
    if (prevBlock) nextHeader = prevBlock.querySelector('.block-header');
  }

  if (nextHeader) {
    selectedHeader.classList.remove('selected');
    nextHeader.classList.add('selected');
    selectedHeader = nextHeader;

    // 選択行を見える位置にスクロール（必要なら）
    selectedHeader.scrollIntoView({ behavior: 'smooth', block: 'center' });

    // infoPanel を更新
    const context_vars = selectedHeader.nextElementSibling.innerHTML;
    const context_formulas = selectedHeader.nextElementSibling.nextElementSibling.innerHTML;
    infoContent.innerHTML = `Selected line: ${selectedHeader.innerHTML}<br>context.vars: ${context_vars}<br>context.formulas: ${context_formulas}`;
    MathJax.typesetPromise();
  }
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
