// Apply saved/preferred theme immediately to prevent flash
(function () {
  var saved = localStorage.getItem('theme');
  var prefersDark = window.matchMedia('(prefers-color-scheme: dark)').matches;
  document.documentElement.setAttribute('data-theme', saved || (prefersDark ? 'dark' : 'light'));
})();

function updateThemeIcon(theme) {
  var icon = document.getElementById('theme-icon');
  if (!icon) return;
  icon.src = theme === 'dark' ? '/tcslib/static/sun.svg' : '/tcslib/static/moon.svg';
}

document.addEventListener('DOMContentLoaded', function () {
  var btn = document.getElementById('theme-toggle');
  if (!btn) return;
  updateThemeIcon(document.documentElement.getAttribute('data-theme'));
  btn.addEventListener('click', function () {
    var next = document.documentElement.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
    document.documentElement.setAttribute('data-theme', next);
    localStorage.setItem('theme', next);
    updateThemeIcon(next);
  });
});
